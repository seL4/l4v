#!/usr/bin/python3
#
# Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

""" Script for bumping seL4 revision in verification-manifest"""

import sys
import argparse
import re


def parseargs():
    """Parse script args"""
    parser = argparse.ArgumentParser(
        description="Bump the seL4 revision in the verification manifest")
    parser.add_argument('-m', '--manifest', required=True,
                        help='Path to the manifest file')
    parser.add_argument('-r', '--revision', required=True,
                        help='New kernel revision hash')

    args = parser.parse_args()
    return args


def main():
    args = parseargs()

    with open(args.manifest, 'r') as manifest:
        lines = manifest.readlines()

    with open(args.manifest, 'w') as manifest:
        found = False
        for line in lines:
            if re.match(r'  \<project name="seL4" revision="[a-f0-9]{40}', line) and not found:
                found = True
                manifest.write(re.sub('revision="[a-f0-9]{40}',
                                      'revision="' + args.revision, line))
            else:
                manifest.write(line)

    if not found:
        print("Could not find seL4 project in manifest file")
        print("Reverting to previous manifest.")

        open(args.manifest, 'w').writelines(lines)
        exit(1)


if __name__ == '__main__':
    sys.exit(main())
