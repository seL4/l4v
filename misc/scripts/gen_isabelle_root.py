#!/usr/bin/env python3
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

#
# Generate an Isabelle "ROOT" build file containing all examples
# in the given directories.
#

import os
import optparse
import glob

# Parse arguments
parser = optparse.OptionParser()
parser.add_option("-o", "--output", dest="output",
                  help="output file", metavar="FILE")
parser.add_option("-i", "--input-dir", dest="input_dir",
                  help="input directory", action="append", default=[],
                  metavar="DIR")
parser.add_option("-s", "--session-name", dest="session_name",
                  help="isabelle session name", metavar="NAME")
parser.add_option("-b", "--base-session", dest="base_session",
                  help="isabelle base session", metavar="NAME")
parser.add_option("-d", "--named-session-dependency", dest="session_dependencies",
                  help="additional named session dependency", action="append", default=[],
                  metavar="NAME")
parser.add_option("-q", "--quick-and-dirty", dest="quick_and_dirty",
                  help="ROOT file should compile with \"quick and dirty\" enabled.",
                  action="store_true", default=False)
parser.add_option("-T", "--generate-theory", dest="theory_file",
                  action="store_true", default=False,
                  help="Generate a theory file instead of a ROOT file.")
parser.add_option("--dir", dest="dirs",
                  help="additional session directory", action="append",
                  default=[], metavar="NAME")
(options, args) = parser.parse_args()

# Check arguments
if len(args) != 0:
    parser.error("Additional arguments passed in.")
if options.output == None:
    parser.error("Require an output filename.")
if len(options.input_dir) == 0:
    parser.error("Require at least one input directory.")
if options.session_name == None and not options.theory_file:
    parser.error("Require a session name.")
if options.base_session == None and not options.theory_file:
    parser.error("Require a base session.")
output_dir = os.path.dirname(options.output)

# Generate ROOT file.
with open(options.output, "w") as output:
    # Fetch list of files to test.
    theories = []
    for d in options.input_dir:
        theories += sorted(glob.glob(os.path.join(d, "*.thy")))

    if options.theory_file:
        session_name = os.path.splitext(os.path.basename(options.output))[0]

        def import_name(file):
            return os.path.splitext(os.path.relpath(file, os.path.dirname(options.output)))[0]

        # Write a theory file.
        output.write("theory %s imports\n" % session_name)
        for i in theories:
            # Theories have the ".thy" stripped off.
            output.write("  \"%s\"\n" % import_name(i))
        output.write("begin\n")
        output.write("\n")
        output.write("end\n")
    else:
        # Write our ROOT file.
        output.write("session \"%s\" = \"%s\" +\n" % (options.session_name, options.base_session))
        if options.session_dependencies:
            output.write("  sessions\n")
            for i in options.session_dependencies:
                output.write("    \"%s\"\n" % i)
        if options.dirs:
            output.write("  directories\n")
            for i in options.dirs:
                output.write("    \"%s\"\n" % i)
        if options.quick_and_dirty:
            output.write("  theories [quick_and_dirty]\n")
        else:
            output.write("  theories\n")
        for i in theories:
            # Theories have the ".thy" stripped off.
            thy = os.path.relpath(i, output_dir)
            thy = os.path.splitext(thy)[0]
            output.write("    \"%s\"\n" % thy)
