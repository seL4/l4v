#!/usr/bin/env python
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

from __future__ import print_function
import pexpect
import optparse
import re
import sys


def main():
    # Parse arguments.
    parser = optparse.OptionParser(usage="usage: %prog [options] <thy file>")
    parser.add_option("-v", "--verbose", dest="verbose",
                      help="Show Isabelle output", action="store_true", default=False)
    (options, args) = parser.parse_args()
    if len(args) != 1:
        parser.error("Expected a single argument containing the Isabelle theory file to run.")

    # Get the filename, and strip off the trailing ".thy".
    filename = args[0]
    if filename.endswith(".thy"):
        filename = filename[:-4]

    # Run Isabelle.
    process = pexpect.spawn('isabelle-process',
                            ['-r', '-q', '-f', '-e', 'use_thy \"%s\";' % filename, "Benchmark"], timeout=None)
    if not options.verbose:
        process.logfile = None
    else:
        process.logfile = sys.stdout

    # Print header.
    header = "%s Benchmark Results" % filename
    print()
    print(header)
    print("=" * len(header))

    # Wait for things to happen.
    errors_detected = False
    while True:
        result = process.expect([
            re.compile('^result:: (.*)$', re.MULTILINE),
            re.compile('^category:: (.*)$', re.MULTILINE),
            re.compile('^\*\*\* (.*)$', re.MULTILINE),
            pexpect.EOF
        ])
        if result == 0:
            # Benchmark result.
            print("    " + process.match.group(1).strip("\r\n"))
        elif result == 1:
            # Category
            print()
            category = process.match.group(1).strip("\r\n")
            print(category)
            print("-" * len(category))
            print()
        elif result == 2:
            # Error
            if not errors_detected:
                print("*** ERROR DETECTED")
            errors_detected = True
        else:
            # EOF
            print
            break

    # Exit
    if errors_detected:
        print("Errors during benchmark process.")
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
