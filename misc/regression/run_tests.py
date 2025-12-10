#!/usr/bin/env python3
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

#
# Very simple command-line test runner.
#

from __future__ import print_function

import argparse
import atexit
import datetime
import collections
import cpuusage
import fnmatch
import memusage
import os
try:
    import Queue
except ImportError:
    import queue
    Queue = queue
import signal
import subprocess
import sys
import testspec
import threading
import time
import traceback
import warnings
import xml.etree.ElementTree as ET

import psutil
if not hasattr(psutil.Process, "children"):
    # psutil API change
    psutil.Process.children = getattr(psutil.Process, "get_children")

ANSI_RESET = "\033[0m"
ANSI_RED = "\033[31;1m"
ANSI_GREEN = "\033[32m"
ANSI_YELLOW = "\033[33m"
ANSI_BRIGHT_YELLOW = "\033[0;93m"
ANSI_WHITE = "\033[37m"
ANSI_BOLD = "\033[1m"


def running_on_github():
    return os.environ.get("GITHUB_REPOSITORY") != None


def output_color(color, s, github=running_on_github()):
    """Wrap the given string in the given color."""
    if sys.stdout.isatty() or github:
        return color + s + ANSI_RESET
    return s

# Find a command in the PATH.


def which(filename):
    for path in os.environ["PATH"].split(os.pathsep):
        candidate = os.path.join(path, filename)
        if os.path.exists(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None


# Warn user if skip_proofs is set (Isabelle won't prove anything)

# run_tests invokes us with cwd set to top-level l4v/run_tests script
ISABELLE = "./isabelle/bin/isabelle"


def warn_isabelle_skip_proofs():
    try:
        out = subprocess.run([ISABELLE, "options", "-g", "skip_proofs"],
                             capture_output=True, text=True, check=True)
        if out.stdout.strip() == 'true':
            print(output_color(ANSI_BRIGHT_YELLOW,
                               "Warning: skip_proofs set in isabelle preferences"))
    except:
        # if Isabelle isn't available/working, Isabelle-related tests will
        # fail, and non-Isabelle-related tests will still run so we don't want
        # to say anything.
        pass


#
# Kill a process and all of its children.
#
# We attempt to handle races where a PID goes away while we
# are looking at it, but not where a PID has been reused.
#


def kill_family(grace_period, parent_pid):
    # Find process.
    try:
        process = psutil.Process(parent_pid)
    except psutil.NoSuchProcess:
        # Race. Nothing more to do.
        return

    process_list = [process]
    for child in process.children(recursive=True):
        process_list.append(child)

    # Grace period for processes to clean up.
    if grace_period > 0:
        for p in process_list[:]:
            try:
                p.send_signal(signal.SIGINT)
            except psutil.NoSuchProcess:
                # Race
                process_list.remove(p)

        # Sleep up to grace_period, but possibly shorter
        slept = 0
        intvl = min(grace_period, 1.0)
        while slept < grace_period:
            if not process.is_running():
                break
            time.sleep(intvl)
            slept += intvl

    # SIGSTOP everyone first.
    for p in process_list[:]:
        try:
            p.suspend()
        except psutil.NoSuchProcess:
            # Race.
            process_list.remove(p)

    # Now SIGKILL everyone.
    process_list.reverse()
    for p in process_list:
        p.send_signal(signal.SIGKILL)


# Process statuses
(RUNNING,     # Still running
 PASSED,      # Passed
 FAILED,      # Failed
 SKIPPED,     # Failed dependencies
 ERROR,       # Failed to run test at all
 TIMEOUT,     # Wall timeout
 CPU_TIMEOUT,  # CPU timeout
 STUCK,       # No CPU activity detected
 CANCELLED    # Cancelled for external reasons
 ) = range(9)

# for print_test_line
status_name = ['RUNNING (***bug***)',
               'passed',
               'FAILED',
               'SKIPPED',
               'ERROR',
               'TIMEOUT',
               'TIMEOUT',
               'STUCK',
               'CANCELLED']
status_maxlen = max(len(s) for s in status_name[1:]) + len(" *")


def run_test(test, status_queue, kill_switch,
             verbose=False, stuck_timeout=None,
             timeout_scale=1.0, timeouts_enabled=True,
             grace_period=0, github=False):
    '''
    Run a single test.

    Return a dict of (name, status, output, cpu time, elapsed time, memory usage).
    This is placed onto the given queue.

    Log only contains the output if verbose is *false*; otherwise, the
    log is output to stdout where we can't easily get to it.

    kill_switch is a threading.Event that is set if the
    --fail-fast feature is triggered from some other thread.
    '''

    # Construct the base command.
    command = ["bash", "-c", test.command]

    # If we have a "pidspace" program, use that to ensure that programs
    # that double-fork can't continue running after the parent command
    # dies.
    if which("pidspace") is not None:
        command = [which("pidspace"), "--"] + command

    # Print command and path.
    if verbose:
        if github:
            print("::group::" + test.name)
        print("\n")
        if os.path.abspath(test.cwd) != os.path.abspath(os.getcwd()):
            path = " [%s]" % os.path.relpath(test.cwd)
        else:
            path = ""
        print("    command: %s%s" % (test.command, path))
        sys.stdout.flush()

    # Determine where stdout should go. We can't print it live to stdout and
    # also capture it, unfortunately.
    output = sys.stdout if verbose else subprocess.PIPE

    # Start timing.
    start_time = datetime.datetime.now()

    # Start the command.
    peak_mem_usage = None
    try:
        process = subprocess.Popen(command,
                                   stdout=output, stderr=subprocess.STDOUT, stdin=subprocess.PIPE,
                                   cwd=test.cwd)
    except:
        output = "Exception while running test:\n\n%s" % (traceback.format_exc())
        if verbose:
            print(output)
            sys.stdout.flush()
        status_queue.put({'name': test.name,
                          'status': ERROR,
                          'output': output,
                          'real_time': datetime.datetime.now() - start_time,
                          'cpu_time': 0,
                          'mem_usage': peak_mem_usage})
        return

    # Now running the test.
    # Wrap in a list to prevent nested functions getting the wrong scope
    test_status = [RUNNING]

    # If we exit for some reason, attempt to kill our test processes.
    def emergency_stop():
        if test_status[0] is RUNNING:
            kill_family(grace_period, process.pid)
    atexit.register(emergency_stop)

    # Setup a timer for the timeout.
    def do_timeout():
        if test_status[0] is RUNNING:
            test_status[0] = TIMEOUT
            kill_family(grace_period, process.pid)

    scaled_test_timeout = test.timeout * timeout_scale
    timer = None
    if timeouts_enabled and scaled_test_timeout > 0:
        timer = threading.Timer(scaled_test_timeout, do_timeout)
        timer.start()

    # Poll the kill switch.
    def watch_kill_switch():
        while True:
            interval = 1.0
            if test_status[0] is not RUNNING:
                break
            if kill_switch.wait(1):
                if test_status[0] is not RUNNING:
                    break
                test_status[0] = CANCELLED
                kill_family(grace_period, process.pid)
            time.sleep(interval)
    kill_switch_thread = threading.Thread(target=watch_kill_switch)
    kill_switch_thread.daemon = True
    kill_switch_thread.start()

    scaled_cpu_timeout = test.cpu_timeout * timeout_scale
    with cpuusage.process_poller(process.pid) as c:
        # Inactivity timeout
        low_cpu_usage = 0.05  # 5%
        cpu_history = collections.deque()  # sliding window
        cpu_usage_total = [0]  # workaround for variable scope

        # Also set a CPU timeout. We poll the cpu usage periodically.
        def cpu_timeout():
            last_cpu_usage = 0
            interval = min(0.5, scaled_cpu_timeout / 10.0)
            while test_status[0] is RUNNING:
                thread_cpu_usage = c.cpu_usage()

                if stuck_timeout:
                    # append to window
                    now = time.time()
                    if not cpu_history:
                        cpu_history.append((time.time(), thread_cpu_usage / interval))
                    else:
                        real_interval = now - cpu_history[-1][0]
                        cpu_increment = thread_cpu_usage - last_cpu_usage
                        cpu_history.append((now, cpu_increment / real_interval))
                    cpu_usage_total[0] += cpu_history[-1][1]

                    # pop from window, ensuring that window covers at least stuck_timeout interval
                    while len(cpu_history) > 1 and cpu_history[1][0] + stuck_timeout <= now:
                        cpu_usage_total[0] -= cpu_history[0][1]
                        cpu_history.popleft()

                    if (now - cpu_history[0][0] >= stuck_timeout and
                            cpu_usage_total[0] / len(cpu_history) < low_cpu_usage):
                        test_status[0] = STUCK
                        kill_family(grace_period, process.pid)
                        break

                if thread_cpu_usage > scaled_cpu_timeout:
                    test_status[0] = CPU_TIMEOUT
                    kill_family(grace_period, process.pid)
                    break

                last_cpu_usage = thread_cpu_usage
                time.sleep(interval)

        cpu_timer = None
        if timeouts_enabled and scaled_cpu_timeout > 0:
            cpu_timer = threading.Thread(target=cpu_timeout)
            cpu_timer.daemon = True
            cpu_timer.start()

        with memusage.process_poller(process.pid) as m:
            # Wait for the command to finish.
            (output, _) = process.communicate()
            peak_mem_usage = m.peak_mem_usage()
            cpu_usage = c.cpu_usage()

        if process.returncode == 0:
            test_status[0] = PASSED
        elif test_status[0] is RUNNING:
            # No special status, so assume it failed by itself
            test_status[0] = FAILED

        if cpu_timer is not None:
            # prevent cpu_timer using c after it goes away
            cpu_timer.join()

    # Cancel the timer. Small race here (if the timer fires just after the
    # process finished), but the return code of our process should still be 0,
    # and hence we won't interpret the result as a timeout.
    if timer is not None and test_status[0] is not TIMEOUT:
        timer.cancel()

    if output is None:
        output = b''
    output = output.decode(encoding='utf8', errors='replace')
    if test_status[0] in [STUCK, TIMEOUT, CPU_TIMEOUT]:
        output = output + extra_timeout_output(test.name)

    if verbose and github:
        print("::endgroup::")
        sys.stdout.flush()

    status_queue.put({'name': test.name,
                      'status': test_status[0],
                      'output': output,
                      'real_time': datetime.datetime.now() - start_time,
                      'cpu_time': cpu_usage,
                      'mem_usage': peak_mem_usage})

# run a heuristic script for getting some output on a timeout


def extra_timeout_output(test_name):
    # we expect the script to be in the same directory as run_tests.py
    here = os.path.dirname(os.path.abspath(__file__))
    command = [os.path.join(here, 'timeout_output'), test_name]
    try:
        process = subprocess.Popen(command,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (output, _) = process.communicate()
        return output.decode('utf8')
    except Exception as e:
        return ("Exception launching timeout_output: %s" % str(e))

# Print a status line.


def print_test_line_start(test_name):
    if sys.stdout.isatty():
        print("  Started %-25s " % (test_name + " ..."))
        sys.stdout.flush()


def print_test_line(test_name, color, status, real_time=None, cpu_time=None, mem=None):
    if mem is not None:
        # Report memory usage in gigabytes.
        mem = '%5.2fGB' % round(float(mem) / 1024 / 1024 / 1024, 2)

    if real_time is not None:
        # Format times as H:MM:SS; strip milliseconds for better printing.
        real_time = datetime.timedelta(seconds=int(real_time.total_seconds()))
        real_time = '%8s real' % real_time

    if cpu_time is not None:
        cpu_time = datetime.timedelta(seconds=int(cpu_time))
        cpu_time = '%8s cpu' % cpu_time

    extras = ', '.join(filter(None, [real_time, cpu_time, mem]))

    # Print status line.
    front = '  Finished %-25s ' % test_name
    status_str = status_name[status]
    if status is not PASSED:
        status_str += " *"
    print(front +
          output_color(color, "{:<{}} ".format(status_str, status_maxlen)) +
          ('(%s)' % extras if extras else ''))
    sys.stdout.flush()

#
# Recursive glob
#


def rglob(base_dir, pattern):
    matches = []
    extras = []
    for root, dirnames, filenames in os.walk(base_dir):
        for filename in fnmatch.filter(filenames, pattern):
            matches.append(os.path.join(root, filename))
        for filename in fnmatch.filter(filenames, 'extra_tests'):
            f = os.path.join(root, filename)
            extras.extend([os.path.join(root, l.strip())
                           for l in open(f) if l.strip()])
    matches.extend([f for e in extras for f in rglob(e, pattern)])
    return sorted(set(matches))

# Print info about tests.


def print_tests(msg, tests, verbose):
    if verbose:
        print('%d tests %s:' % (len(tests), msg))
    for t in tests:
        print(t.name)
        if verbose:
            print('  #> cd ' + t.cwd)
            print('  #> ' + t.command)
            print('  -- depends: %s' % list(t.depends))


def print_test_deps(tests):
    print('digraph "tests" {')
    for t in tests:
        for t_dep in t.depends:
            print('  "%s" -> "%s";' % (t_dep, t.name))
    print('}')

#
# Run tests.
#


def main():
    # Parse arguments
    parser = argparse.ArgumentParser(description="Parallel Regression Framework",
                                     epilog="RUN_TESTS_DEFAULT can be used to overwrite the default set of tests")
    parser.add_argument("-d", "--directory", action="store",
                        metavar="DIR", help="directory to search for test files",
                        default=os.getcwd())
    parser.add_argument("--brief", action="store_true",
                        help="don't print failure logs at end of test run")
    parser.add_argument("-f", "--fail-fast", action="store_true",
                        help="exit once the first failure is detected")
    parser.add_argument("-j", "--jobs", type=int, default=1,
                        help="Number of tests to run in parallel")
    parser.add_argument("-l", "--list", action="store_true",
                        help="list all known tests (-v for details)")
    parser.add_argument("-L", "--dry-run", action="store_true",
                        help="list tests to be run (-v for details)")
    parser.add_argument("--no-dependencies", action="store_true",
                        help="don't check for dependencies when running specific tests")
    parser.add_argument("-x", "--exclude", action="append", metavar="TEST", default=[],
                        help="exclude the given test; tests depending on it may still run")
    parser.add_argument("-r", "--remove", action="append", metavar="TEST", default=[],
                        help="remove the given test and tests that depend on it")
    parser.add_argument("-v", "--verbose", action="store_true",
                        help="print test output or list more details")
    parser.add_argument("--dot", action="store_true",
                        help="for -l or -L, output test dependencies in GraphViz format")
    parser.add_argument("--junit-report", metavar="FILE",
                        help="write JUnit-style test report")
    parser.add_argument("--stuck-timeout", type=int, default=600, metavar='N',
                        help="timeout tests if not using CPU for N seconds (default: 600)")
    timeout_mod_args = parser.add_mutually_exclusive_group()
    timeout_mod_args.add_argument("--scale-timeouts", type=float, default=1, metavar='N',
                                  help="multiply test timeouts by N (e.g. 2 provides twice as much time)")
    timeout_mod_args.add_argument("--no-timeouts", action="store_true",
                                  help="do not enforce any test timeouts")
    parser.add_argument("--grace-period", type=float, default=5, metavar='N',
                        help="interrupt over-time processes N seconds before killing them (default: 5)")
    parser.add_argument("tests", metavar="TESTS",
                        help="select these tests to run (defaults to all tests)",
                        nargs="*")
    args = parser.parse_args()

    if args.jobs < 1:
        parser.error("Number of parallel jobs must be at least 1")

    if args.scale_timeouts <= 0:
        parser.error("--scale-timeouts value must be greater than 0")

    github = running_on_github()

    # Search for test files:
    test_xml = sorted(rglob(args.directory, "tests.xml"))
    test_info = testspec.process_test_files(test_xml)
    all_tests = test_info.tests

    # List test names if requested.
    if args.list:
        if args.dot:
            print_test_deps(all_tests)
        else:
            print_tests('total', all_tests, args.verbose)
        sys.exit(0)

    warn_isabelle_skip_proofs()

    # Calculate which tests should be run.
    desired_names = set(args.tests) or set(os.environ.get('RUN_TESTS_DEFAULT', '').split())
    bad_names = desired_names - set([t.name for t in all_tests])
    if bad_names:
        parser.error("These tests are requested, but do not exist: %s" %
                     (", ".join(sorted(bad_names))))

    def get_tests(names):
        '''Given a set of names, return the corresponding set of Tests.'''
        return {t for t in all_tests if t.name in names}

    def add_deps(x):
        '''Given a set of Tests, add all dependencies to it.'''
        x.update({t for w in x for t in add_deps(get_tests(w.depends))})
        return x

    if desired_names:
        tests_to_run_set = get_tests(desired_names)
    else:
        tests_to_run_set = set(all_tests)

    # Are we skipping dependencies? If not, add them.
    if not args.no_dependencies:
        add_deps(tests_to_run_set)

    # Preserve the order of the original set of Tests.
    tests_to_run = [t for t in all_tests if t in tests_to_run_set]

    # Process --exclude'd tests.
    exclude_tests = set(args.exclude)
    tests_to_run = [t for t in tests_to_run if t.name not in exclude_tests]

    # Process --remove'd tests transitively.
    remove_trans = frozenset.union(frozenset(), *[
        test_info.reverse_deps.rtrans(r, lambda x: frozenset())
        for r in args.remove])
    conflict_names = {t for t in desired_names if t not in exclude_tests and t in remove_trans}
    if conflict_names:
        # It's unclear what we should do if a selected test has been --removed.
        # For now, just bail out.
        parser.error(
            "Cannot run these tests because they depend on removed tests: %s\n" %
            ", ".join(sorted(conflict_names))
            + "(The removed tests are: %s)" %
            ", ".join(args.remove))
    tests_to_run = [t for t in tests_to_run if t.name not in remove_trans]

    bad_names = set.union(exclude_tests, set(args.remove)) - {t.name for t in all_tests}
    if bad_names:
        sys.stderr.write("Warning: These tests are excluded/removed, but do not exist: %s\n" %
                         (", ".join(sorted(bad_names))))
        sys.stderr.flush()

    if args.dry_run:
        if args.dot:
            print_test_deps(tests_to_run)
        else:
            print_tests('selected', tests_to_run, args.verbose)
        sys.exit(0)

    # Run the tests.
    print("Running %d test(s)..." % len(tests_to_run))
    failed_tests = set()
    passed_tests = set()
    test_results = {}

    # Use a simple list to store the pending queue. We track the dependencies separately.
    tests_queue = tests_to_run[:]
    # Current jobs.
    current_jobs = {}
    # Newly finished jobs.
    status_queue = Queue.Queue()

    # If run from a tty and -v is off, we also track
    # current jobs on the bottom line of the tty.
    # We cache this status line to help us wipe it later.
    tty_status_line = [""]

    def wipe_tty_status():
        if tty_status_line[0]:
            print(" " * len(tty_status_line[0]) + "\r", end="")
            sys.stdout.flush()
            tty_status_line[0] = ""

    # Handle --fail-fast
    kill_switch = threading.Event()

    while tests_queue or current_jobs:
        # Update status line with pending jobs.
        if current_jobs and sys.stdout.isatty() and not args.verbose:
            tty_status_line[0] = "Running: " + ", ".join(sorted(current_jobs.keys()))
            print(tty_status_line[0] + "\r", end="")
            sys.stdout.flush()

        # Check if we have a job slot.
        if len(current_jobs) < args.jobs:
            # Find the first non-blocked test and handle it.
            for i, t in enumerate(tests_queue):
                # Leave out dependencies that were excluded at the command line.
                real_depends = t.depends & set(t.name for t in tests_to_run)
                # Non-blocked but depends on a failed test. Remove it.
                if (len(real_depends & failed_tests) > 0
                    # --fail-fast triggered, fail all subsequent tests
                        or kill_switch.is_set()):

                    wipe_tty_status()
                    print_test_line(t.name, ANSI_YELLOW, SKIPPED)
                    failed_tests.add(t.name)
                    del tests_queue[i]
                    break
                # Non-blocked and open. Start it.
                if real_depends.issubset(passed_tests):
                    test_thread = threading.Thread(
                        target=run_test, name=t.name,
                        args=(t, status_queue, kill_switch,
                              args.verbose, args.stuck_timeout,
                              args.scale_timeouts, not args.no_timeouts,
                              args.grace_period, github))
                    wipe_tty_status()
                    print_test_line_start(t.name)
                    test_thread.start()
                    current_jobs[t.name] = test_thread
                    del tests_queue[i]
                    break

        # Wait for jobs to complete.
        try:
            while True:
                info = status_queue.get(block=True, timeout=0.1337)  # Built-in pause
                name, status = info['name'], info['status']

                test_results[name] = info
                del current_jobs[name]

                # Print result.
                wipe_tty_status()
                if status is PASSED:
                    passed_tests.add(name)
                    colour = ANSI_GREEN
                elif status is CANCELLED:
                    failed_tests.add(name)
                    colour = ANSI_YELLOW
                else:
                    failed_tests.add(name)
                    colour = ANSI_RED
                print_test_line(name, colour, status,
                                real_time=info['real_time'],
                                cpu_time=info['cpu_time'],
                                mem=info['mem_usage'])
                if args.fail_fast and status != PASSED:
                    # Notify current threads and future tests
                    kill_switch.set()
        except Queue.Empty:
            pass
    wipe_tty_status()

    # Print failure summaries unless requested not to.
    if not args.brief and len(failed_tests) > 0:
        LINE_LIMIT = 40

        def print_line():
            print("".join(["-" for x in range(72)]))
        print("")
        # Sort failed_tests according to tests_to_run
        for t in tests_to_run:
            if t.name not in failed_tests:
                continue
            if t.name not in test_results:
                continue

            print_line()
            print("TEST %s: %s" % (status_name[test_results[t.name]['status']], t.name))
            print("")
            output = test_results[t.name]['output'].rstrip("\n")
            if output:
                lines = output.split("\n") + ['']
            else:
                lines = ['(no output)']
            if len(lines) > LINE_LIMIT:
                lines = ["..."] + lines[-LINE_LIMIT:]
            print("\n".join(lines))
        print_line()

    # Print JUnit-style test report.
    # reference: https://github.com/notnoop/hudson-tools/blob/master/toJunitXML/sample-junit.xml
    if args.junit_report is not None:
        testsuite = ET.Element("testsuite")
        for t in tests_to_run:
            if t.name not in test_results:
                # test was skipped
                testcase = ET.SubElement(testsuite, "testcase",
                                         classname="", name=t.name, time="0")
                if t.depends & failed_tests:
                    ET.SubElement(testcase, "error", type="error").text = (
                        "Failed dependencies: " + ', '.join(t.depends & failed_tests))
                else:
                    ET.SubElement(testcase, "error", type="error").text = "Cancelled"
            else:
                info = test_results[t.name]
                testcase = ET.SubElement(testsuite, "testcase",
                                         classname="", name=t.name, time='%f' % info['real_time'].total_seconds())
                if info['status'] is PASSED:
                    if not args.verbose:
                        ET.SubElement(testcase, "system-out").text = info['output']
                elif info['status'] is FAILED:
                    ET.SubElement(testcase, "failure", type="failure").text = info['output']
                elif info['status'] in (TIMEOUT, CPU_TIMEOUT):
                    ET.SubElement(testcase, "error", type="timeout").text = info['output']
                elif info['status'] is STUCK:
                    ET.SubElement(testcase, "error", type="stuck").text = info['output']
                elif info['status'] is CANCELLED:
                    ET.SubElement(testcase, "error", type="cancelled").text = info['output']
                elif info['status'] is ERROR:
                    ET.SubElement(testcase, "error", type="error").text = info['output']
                else:
                    warnings.warn("Unknown status code: {}".format(info['status']))
                    ET.SubElement(testcase, "error", type="unknown").text = info['output']

        ET.ElementTree(testsuite).write(args.junit_report)

    # Print summary.
    print(("\n\n"
           + output_color(ANSI_WHITE, "%d/%d tests succeeded.") + "\n")
          % (len(tests_to_run) - len(failed_tests), len(tests_to_run)))
    if len(failed_tests) > 0:
        print(output_color(ANSI_RED, "Tests failed.") + "\n")
        if kill_switch.is_set():
            print("Exiting early due to --fail-fast.")
        sys.exit(1)
    else:
        print(output_color(ANSI_GREEN, "All tests passed.") + "\n")
        sys.exit(0)


if __name__ == "__main__":
    main()
