#!/usr/bin/env python3
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
Monitors the total CPU usage of a process and its children. Usage is similar
to the UNIX `time` utility.

NB: In order to get up-to-date information, we don't use interfaces such
    as os.times, which only includes terminated and waited-for children.
    Instead, we poll the process tree regularly. This means that when a
    child process dies, its CPU time since the last poll is lost and not
    included in the total time.

    Hence the total reported time will be an underestimate of the true
    CPU usage, especially for short-lived child processes.
'''

from __future__ import print_function
import os
import psutil
import signal
import subprocess
import sys
import threading
import time
import warnings

try:
    import psutil
    if not hasattr(psutil.Process, "children") and hasattr(psutil.Process, "get_children"):
        psutil.Process.children = psutil.Process.get_children
    if not hasattr(psutil.Process, "memory_maps") and hasattr(psutil.Process, "get_memory_maps"):
        psutil.Process.memory_maps = psutil.Process.get_memory_maps

except ImportError:
    print("Error: 'psutil' module not available. Run\n"
          "\n"
          "    pip3 install --user psutil\n"
          "\n"
          "to install.", file=sys.stderr)
    sys.exit(1)

# The psutil.Process.cpu_times() API changed at version 4.1.0.
# Earlier versions give the user and system times for the queried
# process only. Later versions return two additional tuple members
# for the total user and system times of its child processes.
# For compatibility with both versions, we ignore the additional
# values.


def cpu_time_of(process):
    cpu_times = process.cpu_times()
    return cpu_times[0] + cpu_times[1]


class Poller(threading.Thread):
    '''Subclass of threading.Thread that monitors CPU usage of another process.
       Use run() to start the process.
       Use cpu_usage() to retrieve the latest estimate of CPU usage.'''

    def __init__(self, pid):
        super(Poller, self).__init__()
        # Daemonise ourselves to avoid delaying exit of the process of our
        # calling thread.
        self.daemon = True
        self.pid = pid
        self.finished = False
        self.started = threading.Semaphore(0)
        self.proc = None

        # Reported stat.
        self.cpu = 0.0

        # Remember CPU times of recently seen children.
        # This is to prevent double-counting for child processes.
        self.current_children = {}  # {(pid, create_time): CPU time}
        # CPU time of dead children is recorded here.
        self.old_children_cpu = 0.0

    def run(self):
        def update():
            total = 0.0

            # Fetch process's usage.
            try:
                if self.proc is None:
                    self.proc = psutil.Process(self.pid)
                total += cpu_time_of(self.proc)

                # Fetch children's usage.
                new_current_children = {}
                for c in self.proc.children(recursive=True):
                    try:
                        t = cpu_time_of(c)
                        new_current_children[(c.pid, c.create_time())] = t
                        total += t
                    except psutil.NoSuchProcess:
                        pass
                    except psutil.AccessDenied:
                        pass

                # For children that are no longer running, remember their
                # most recently recorded CPU time.
                reaped_cpu = 0.0
                for c_id, c_t in self.current_children.items():
                    if c_id not in new_current_children:
                        reaped_cpu += c_t
                self.old_children_cpu += reaped_cpu
                self.current_children = new_current_children
                total += self.old_children_cpu

            except psutil.AccessDenied as err:
                warnings.warn("access denied: pid=%d" % err.pid, RuntimeWarning)

            # Add 1 ns allowance for floating-point rounding, which occurs when we
            # accumulate current_children times for dead processes into reaped_cpu.
            # (Floating point epsilon is about 1e-15.)
            if total + 1e-9 < self.cpu:
                try:
                    cmd = repr(' '.join(self.proc.cmdline()))
                except Exception:
                    cmd = '??'
                warnings.warn("cpu non-monotonic: %.15f -> %.15f, pid=%d, cmd=%s" %
                              (self.cpu, total, self.pid, cmd),
                              RuntimeWarning)
            return total

        # Fetch a sample, and notify others that we have started.
        self.cpu = update()
        self.started.release()

        # Poll the process periodically.
        #
        # We poll quickly at the beginning and use exponential backout
        # to try and get better stats on short-lived processes.
        #
        polling_interval = 0.01
        max_interval = 0.5
        while not self.finished:
            time.sleep(polling_interval)
            try:
                self.cpu = update()
            except psutil.NoSuchProcess:
                break
            if polling_interval < max_interval:
                polling_interval = min(polling_interval * 1.5, max_interval)

    def cpu_usage(self):
        return self.cpu

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.finished = True


def process_poller(pid):
    '''Initiate polling of a subprocess. This is intended to be used in a
    `with` block.'''
    # Create a new thread and start it up.
    p = Poller(pid)
    p.start()

    # Wait for the thread to record at least one sample before continuing.
    p.started.acquire()

    return p


def main():
    if len(sys.argv) <= 1 or sys.argv[1] in ['-?', '--help']:
        print('Usage: %s command args...\n Measure total CPU '
              'usage of a command' % sys.argv[0], file=sys.stderr)
        return -1

    # Run the command requested.
    try:
        p = subprocess.Popen(sys.argv[1:])
    except OSError:
        print('command not found', file=sys.stderr)
        return -1

    cpu = 0
    m = process_poller(p.pid)
    while True:
        try:
            p.returncode = p.wait()
            break
        except KeyboardInterrupt:
            # The user Ctrl-C-ed us. The child should have received SIGINT;
            # continue waiting for it to finish
            pass

    print('Total cpu %f seconds' % m.cpu_usage(), file=sys.stderr)

    return p.returncode


if __name__ == '__main__':
    sys.exit(main())
