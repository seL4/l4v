#!/usr/bin/env python3
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
Monitors the peak memory usage of a process and its children. Usage is similar
to the UNIX `time` utility.
'''

from __future__ import print_function
import subprocess
import sys
import threading
import time

PSUTIL_NOT_AVAILABLE = False
try:
    import psutil
    if not hasattr(psutil.Process, "children") and hasattr(psutil.Process, "get_children"):
        psutil.Process.children = psutil.Process.get_children
    if not hasattr(psutil.Process, "memory_maps") and hasattr(psutil.Process, "get_memory_maps"):
        psutil.Process.memory_maps = psutil.Process.get_memory_maps

except ImportError:
    PSUTIL_NOT_AVAILABLE = True

if PSUTIL_NOT_AVAILABLE:
    def get_usage(proc):
        return 0

    def get_total_usage(proc):
        return 0
else:
    def get_usage(proc):
        '''Retrieve the memory usage of a particular psutil process without its
        children. We use the proportional set size, which accounts for shared pages
        to give us a more accurate total usage.'''
        assert isinstance(proc, psutil.Process)
        try:
            return sum([m.pss for m in proc.memory_maps(grouped=True)])
        except psutil.AccessDenied:
            # If we don't have permission to read a particular process,
            # just return 0.
            return 0
        except AttributeError:
            # Newer versions of psutil do not support memory_maps on MacOS
            return 0

    def get_total_usage(pid):
        '''Retrieve the memory usage of a process by PID including its children. We
        ignore NoSuchProcess errors to mask subprocesses exiting while the cohort
        continues.'''
        total = 0

        # Fetch parent's usage.
        try:
            p = psutil.Process(pid)
            total += get_usage(p)
            children = p.children(recursive=True)  # pylint: disable=E1123
        except psutil.NoSuchProcess:
            return 0

        # Fetch usage of children.
        for proc in children:
            try:
                total += get_usage(proc)
            except psutil.NoSuchProcess:
                pass

        return total


class Poller(threading.Thread):
    def __init__(self, pid):
        super(Poller, self).__init__()
        # Daemonise ourselves to avoid delaying exit of the process of our
        # calling thread.
        self.daemon = True
        self.pid = pid
        self.high = 0
        self.finished = False
        self.started = threading.Semaphore(0)

    def run(self):
        # Fetch a sample, and notify others that we have started.
        self.high = get_total_usage(self.pid)
        self.started.release()

        #
        # Poll the process periodically to track a high water mark of its
        # memory usage.
        #
        # We poll quickly at the beginning and use exponential backout until we
        # hit 1 second to try and get better stats on short-lived processes.
        #
        polling_interval = 0.01
        while not self.finished:
            time.sleep(polling_interval)
            usage = get_total_usage(self.pid)
            if usage > self.high:
                self.high = usage
            if polling_interval < 1.0:
                polling_interval = min(polling_interval * 1.5, 1.0)

    def peak_mem_usage(self):
        return self.high

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
        print('Usage: %s command args...\n Measure peak memory '
              'usage of a command' % sys.argv[0], out=sys.stderr)
        return -1

    if PSUTIL_NOT_AVAILABLE:
        print("Error: 'psutil' module not available. Run\n"
              "\n"
              "    pip3 install --user psutil\n"
              "\n"
              "to install.")
        sys.exit(1)

    # Run the command requested.
    try:
        p = subprocess.Popen(sys.argv[1:])
    except OSError:
        print('command not found', out=sys.stderr)
        return -1

    high = 0
    try:
        with process_poller(p.pid) as m:  # pylint: disable=E1101
            p.communicate()
            high = m.peak_mem_usage()
    except KeyboardInterrupt:
        # The user Ctrl-C-ed us. Fake an error return code.
        p.returncode = -1

    print('Peak usage %d bytes' % high, out=sys.stderr)

    return p.returncode


if __name__ == '__main__':
    sys.exit(main())
