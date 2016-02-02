#!/usr/bin/env python
#
#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
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
except:
    import queue
    Queue = queue
import signal
import subprocess
import sys
import testspec
import threading
import time
import traceback
import xml.etree.ElementTree as ET

try:
    import psutil
    if not hasattr(psutil.Process, "children") and hasattr(psutil.Process, "get_children"):
        # psutil API change
        psutil.Process.children = psutil.Process.get_children
except ImportError:
    print("Error: failed to import psutil module.\n"
          "To install psutil, try:\n"
          "  pip install --user psutil", file=sys.stderr)
    sys.exit(2)

ANSI_RESET = "\033[0m"
ANSI_RED = "\033[31;1m"
ANSI_GREEN = "\033[32m"
ANSI_YELLOW = "\033[33m"
ANSI_WHITE = "\033[37m"
ANSI_BOLD = "\033[1m"

def output_color(color, s):
    """Wrap the given string in the given color."""
    if sys.stdout.isatty():
        return color + s + ANSI_RESET
    return s

# Find a command in the PATH.
def which(file):
    for path in os.environ["PATH"].split(os.pathsep):
        candidate = os.path.join(path, file)
        if os.path.exists(candidate) and os.access(candidate, os.X_OK):
            return candidate
    return None

#
# Kill a process and all of its children.
#
# We attempt to handle races where a PID goes away while we
# are looking at it, but not where a PID has been reused.
#
def kill_family(parent_pid):
    # Find process.
    try:
        process = psutil.Process(parent_pid)
    except psutil.NoSuchProcess:
        # Race. Nothing more to do.
        return

    # SIGSTOP everyone first.
    try:
        process.suspend()
    except psutil.NoSuchProcess:
        # Race. Nothing more to do.
        return
    process_list = [process]
    for child in process.children(recursive=True):
        try:
            child.suspend()
        except psutil.NoSuchProcess:
            # Race.
            pass
        else:
            process_list.append(child)

    # Now SIGKILL everyone.
    process_list.reverse()
    for p in process_list:
        p.send_signal(signal.SIGKILL)

#
# Run a single test.
#
# Return a dict of (name, status, output, cpu time, elapsed time, memory usage).
# This is placed onto the given queue.
#
# Log only contains the output if verbose is *false*; otherwise, the
# log is output to stdout where we can't easily get to it.
#
def run_test(test, status_queue, verbose=False, stuck_timeout=None):
    # Construct the base command.
    command = ["bash", "-c", test.command]

    # If we have a "pidspace" program, use that to ensure that programs
    # that double-fork can't continue running after the parent command
    # dies.
    if which("pidspace") != None:
        command = [which("pidspace"), "--"] + command

    # Print command and path.
    if verbose:
        print("\n")
        if os.path.abspath(test.cwd) != os.path.abspath(os.getcwd()):
            path = " [%s]" % os.path.relpath(test.cwd)
        else:
            path = ""
        print("    command: %s%s" % (test.command, path))

    # Determine where stdout should go. We can't print it live to stdout and
    # also capture it, unfortunately.
    output = sys.stdout if verbose else subprocess.PIPE

    # Start timing.
    start_time = datetime.datetime.now()

    # Start the command.
    peak_mem_usage = None
    cpu_usage = None
    try:
        process = subprocess.Popen(command,
                stdout=output, stderr=subprocess.STDOUT, stdin=subprocess.PIPE,
                cwd=test.cwd)
    except:
        output = "Exception while running test:\n\n%s" % (traceback.format_exc())
        if verbose:
            print(output)
        return (False, "ERROR", output, datetime.datetime.now() - start_time, peak_mem_usage)

    # If we exit for some reason, attempt to kill our test processes.
    process_running = True
    def emergency_stop():
        if process_running:
            kill_family(process.pid)
    atexit.register(emergency_stop)

    # Setup an alarm at the timeout.
    was_timeout = [False] # Wrap in list to prevent do_timeout getting the wrong variable scope
    was_cpu_timeout = [False] # as above
    def do_timeout():
        was_timeout[0] = True
        kill_family(process.pid)
    timer = threading.Timer(test.timeout, do_timeout)
    if test.timeout > 0:
        timer.start()

    with cpuusage.process_poller(process.pid) as c:
        # Inactivity timeout
        low_cpu_usage = 0.05 # 5% -- FIXME: hardcoded
        cpu_history = collections.deque() # sliding window
        last_cpu_usage = 0
        cpu_usage_total = [0] # workaround for variable scope

        # Also set a CPU timeout. We poll the cpu usage periodically.
        def cpu_timeout():
            interval = min(0.5, test.cpu_timeout / 10.0)
            while process_running:
                cpu_usage = c.cpu_usage()

                if stuck_timeout:
                    # append to window
                    now = time.time()
                    if not cpu_history:
                        cpu_history.append((time.time(), cpu_usage / interval))
                    else:
                        real_interval = now - cpu_history[-1][0]
                        cpu_increment = cpu_usage - last_cpu_usage
                        cpu_history.append((now, cpu_increment / real_interval))
                    cpu_usage_total[0] += cpu_history[-1][1]

                    # pop from window, ensuring that window covers at least stuck_timeout interval
                    while len(cpu_history) > 1 and cpu_history[1][0] + stuck_timeout <= now:
                        cpu_usage_total[0] -= cpu_history[0][1]
                        cpu_history.popleft()

                    if (now - cpu_history[0][0] >= stuck_timeout and
                        cpu_usage_total[0] / len(cpu_history) < low_cpu_usage):
                        was_cpu_timeout[0] = 'stuck'
                        kill_family(process.pid)
                        break

                if cpu_usage > test.cpu_timeout:
                    was_cpu_timeout[0] = 'total'
                    kill_family(process.pid)
                    break

                last_cpu_usage = cpu_usage
                time.sleep(interval)

        if test.cpu_timeout > 0:
            cpu_timer = threading.Thread(target=cpu_timeout)
            cpu_timer.daemon = True
            cpu_timer.start()

        with memusage.process_poller(process.pid) as m:
            # Wait for the command to finish.
            (output, _) = process.communicate()
            peak_mem_usage = m.peak_mem_usage()
            cpu_usage = c.cpu_usage()

        process_running = False
        if test.cpu_timeout > 0:
            cpu_timer.join()

    # Cancel the alarm. Small race here (if the timer fires just after the
    # process finished), but the returncode of our process should still be 0,
    # and hence we won't interpret the result as a timeout.
    if not was_timeout[0]:
        timer.cancel()

    if output == None:
        output = ""
    output = output.decode()
    if process.returncode == 0:
        status = "pass"
    elif was_timeout[0] or was_cpu_timeout[0]:
        if was_cpu_timeout[0] == 'stuck':
            status = "STUCK for %gs" % stuck_timeout
        else:
            status = "TIMEOUT"
    else:
        status = "FAILED"
    status_queue.put({'name': test.name,
                      'status': status,
                      'output': output,
                      'real_time': datetime.datetime.now() - start_time,
                      'cpu_time': cpu_usage,
                      'mem_usage': peak_mem_usage})

# Print a status line.
def print_test_line_start(test_name, legacy=False):
    if legacy:
        return
    if sys.stdout.isatty():
        print("  Started %-25s " % (test_name + " ..."))
        sys.stdout.flush()

def print_test_line(test_name, color, status, real_time=None, cpu_time=None, mem=None, legacy=False):
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
    if legacy:
        front = '  running %-25s ' % (test_name + " ...")
    else:
        front = '  Finished %-25s ' % test_name
    print(front +
          output_color(color, "%-10s" % status) +
          ('(%s)' % extras if extras else ''))
    sys.stdout.flush()

#
# Recursive glob
#
def rglob(base_dir, pattern):
    matches = []
    for root, dirnames, filenames in os.walk(base_dir):
        for filename in fnmatch.filter(filenames, pattern):
            matches.append(os.path.join(root, filename))
    return matches

#
# Run tests.
#
def main():
    # Parse arguments
    parser = argparse.ArgumentParser(description="Parallel Regression Framework")
    parser.add_argument("-s", "--strict", action="store_true",
            help="be strict when parsing test XML files")
    parser.add_argument("-d", "--directory", action="store",
            metavar="DIR", help="directory to search for test files",
            default=os.getcwd())
    parser.add_argument("--brief", action="store_true",
            help="don't print failure logs at end of test run")
    parser.add_argument("-j", "--jobs", type=int, default=1,
            help="Number of tests to run in parallel")
    parser.add_argument("-l", "--list", action="store_true",
            help="list known tests")
    parser.add_argument("--legacy", action="store_true",
            help="use legacy 'IsaMakefile' specs")
    # --legacy-status used by top-level regression-v2 script
    parser.add_argument("--legacy-status", action="store_true",
            help="emulate legacy (sequential code) status lines")
    parser.add_argument("-v", "--verbose", action="store_true",
            help="print test output")
    parser.add_argument("--junit-report", metavar="FILE",
            help="write JUnit-style test report")
    parser.add_argument("--stuck-timeout", type=int, default=600, metavar='N',
            help="timeout tests if not using CPU for N seconds (default: %(default))")
    parser.add_argument("tests", metavar="TESTS",
            help="tests to run (defaults to all tests)",
            nargs="*")
    args = parser.parse_args()

    if args.jobs < 1:
        parser.error("Number of parallel jobs must be at least 1")

    # Search for test files:
    if not args.legacy:
        test_xml = sorted(rglob(args.directory, "tests.xml"))
        tests = testspec.parse_test_files(test_xml, strict=args.strict)
    else:
        # Fetch legacy tests.
        tests = testspec.legacy_testspec(args.directory)

    # List test names if requested.
    if args.list:
        for t in tests:
            print(t.name)
        sys.exit(0)

    # Calculate which tests should be run.
    tests_to_run = []
    if len(args.tests) == 0:
        tests_to_run = tests
    else:
        desired_names = set(args.tests)
        bad_names = desired_names - set([t.name for t in tests])
        if len(bad_names) > 0:
            parser.error("Unknown test names: %s" % (", ".join(sorted(bad_names))))
        tests_to_run = [t for t in tests if t.name in desired_names]

    # Run the tests.
    print("Running %d test(s)..." % len(tests_to_run))
    failed_tests = set()
    passed_tests = set()
    test_results = {}

    # Use a simple list to store the pending queue. We track the dependencies separately.
    tests_queue = tests_to_run[:]
    # Current jobs.
    current_jobs = {}
    # Output status.
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
                # Non-blocked and open. Start it.
                if real_depends.issubset(passed_tests):
                    test_thread = threading.Thread(target=run_test, name=t.name,
                                                   args=(t, status_queue, args.verbose, args.stuck_timeout))
                    wipe_tty_status()
                    print_test_line_start(t.name, args.legacy_status)
                    test_thread.start()
                    current_jobs[t.name] = test_thread
                    popped_test = True
                    del tests_queue[i]
                    break
                # Non-blocked but depends on a failed test. Remove it.
                if len(real_depends & failed_tests) > 0:
                    wipe_tty_status()
                    print_test_line(t.name, ANSI_YELLOW, "skipped", legacy=args.legacy_status)
                    failed_tests.add(t.name)
                    del tests_queue[i]
                    break

        # Wait for jobs to complete.
        try:
            while True:
                info = status_queue.get(block=True, timeout=0.1337) # Built-in pause
                name, status = info['name'], info['status']

                test_results[name] = info
                del current_jobs[name]

                # Print result.
                wipe_tty_status()
                if status != 'pass':
                    failed_tests.add(name)
                    status += " * "
                    colour = ANSI_RED
                else:
                    passed_tests.add(name)
                    colour = ANSI_GREEN
                print_test_line(name, colour, status,
                                real_time=info['real_time'], cpu_time=info['cpu_time'], mem=info['mem_usage'],
                                legacy=args.legacy_status)
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
            print("TEST FAILURE: %s" % t.name)
            print("")
            log = test_results[t.name]['output'].rstrip("\n") + "\n"
            lines = log.split("\n")
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
                ET.SubElement(testcase, "error", type="error").text = (
                    "Failed dependencies: " + ', '.join(t.depends & failed_tests))
            else:
                info = test_results[t.name]
                testcase = ET.SubElement(testsuite, "testcase",
                                         classname="", name=t.name, time='%f' % info['real_time'].total_seconds())
                if info['status'] == "FAILED":
                    ET.SubElement(testcase, "failure", type="failure").text = info['output']
                elif info['status'] == "TIMEOUT":
                    ET.SubElement(testcase, "error", type="timeout").text = info['output']
                elif "STUCK" in info['status']:
                    ET.SubElement(testcase, "error", type="stuck").text = info['output']
                else:
                    if not args.verbose:
                        ET.SubElement(testcase, "system-out").text = info['output']
        ET.ElementTree(testsuite).write(args.junit_report)

    # Print summary.
    print(("\n\n"
            + output_color(ANSI_WHITE, "%d/%d tests succeeded.") + "\n")
            % (len(tests_to_run) - len(failed_tests), len(tests_to_run)))
    if len(failed_tests) > 0:
        print(output_color(ANSI_RED, "Tests failed.") + "\n")
        sys.exit(1)
    else:
        print(output_color(ANSI_GREEN, "All tests passed.") + "\n")
        sys.exit(0)


if __name__ == "__main__":
    main()
