#!/usr/bin/env python
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
# Generate the file "umm_types.txt", required for generating theory files used
# in Isabelle sessions "CSpec" and beyond.
#

import subprocess
import argparse
import os
import sys
import tempfile
import shutil

# Create a temporary directory
class TempDir(object):
    def __enter__(self, cleanup=True):
        self.filename = tempfile.mkdtemp()
        self.cleanup = cleanup
        return self.filename

    def __exit__(self, type, value, traceback):
        if self.cleanup:
            shutil.rmtree(self.filename)
        return False

parser = argparse.ArgumentParser(
        description="Generate a 'umm_types.txt' file from the C parser, required by the bitfield generator.")
parser.add_argument('input', metavar='INPUT', type=str,
        help="C file to parse")
parser.add_argument('output', metavar='OUTPUT', type=str,
        help="output filename")
parser.add_argument('--root', metavar='ROOT', type=str,
        help="add Isabelle ROOT or ROOTS file path", action='append')
args = parser.parse_args()

if "ISABELLE_PROCESS" not in os.environ or "ISABELLE_TOOL" not in os.environ:
    print "Run this from within 'isabelle env'."
    sys.exit(1)

THY_DATA = """
theory UmmTypesFile
  imports CTranslation
begin
declare [[allow_underscore_idents = true]]
setup {* IsarInstall.gen_umm_types_file "%(input)s" "%(output)s" *}
end
"""

ROOT_DATA = """
session UmmTypes = CParser +
  theories UmmTypesFile
  files "%(input)s"
"""

# Create a new theory file and ROOT file in a temporary directory.
with TempDir() as tmp_dir:
    filenames = {
            "input": os.path.abspath(args.input),
            "output": os.path.abspath(args.output),
            }
    with open(os.path.join(tmp_dir, "UmmTypesFile.thy"), "w") as f:
        f.write(THY_DATA % filenames)
    with open(os.path.join(tmp_dir, "ROOT"), "w") as f:
        f.write(ROOT_DATA % filenames)

    # Run Isabelle over it.
    def interleave(a, l):
        result = []
        for x in l:
            result.append(a)
            result.append(x)
        return result
    print "\nGenerating umm_types data file...\n"
    subprocess.check_call([
            os.environ["ISABELLE_TOOL"], "build", "-c"]
                + interleave("-d", [os.path.abspath(x) for x in args.root])
                + ["-d", ".", "-v", "-b", "UmmTypes"],
            cwd=tmp_dir)

