#!/usr/bin/env python3
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import argparse
import errno
import fnmatch
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

# Create a temporary directory


class TempDir():
    def __init__(self, cleanup=True):
        self.cleanup = cleanup

    def __enter__(self):
        self.filename = tempfile.mkdtemp()
        return self.filename

    def __exit__(self, type, value, traceback):
        if self.cleanup:
            shutil.rmtree(self.filename)
        return False


def mkdir_p(path):
    try:
        os.makedirs(path)
    except OSError as exc:
        if exc.errno == errno.EEXIST:
            pass
        else:
            raise


def rglob(base_path, pattern):
    """Recursively find files matching glob pattern 'pattern', from base
    directory 'base_path'."""
    results = []
    for root, dirnames, filenames in os.walk(base_path):
        for filename in fnmatch.filter(filenames, pattern):
            results.append(os.path.join(root, filename))
    return results


def read_manifest(filename, base):
    """Read the files described in a MANIFEST file, which has the form:

    foo/filepattern:
        description

    bar/filepattern:
        description

    and return a list of basedir/file pairs. All filenames are w.r.t.
    the "base" directory.
    """
    results = []
    with open(filename) as f:
        for line in f.readlines():
            line = line.strip("\r\n")
            if not line.startswith(" ") and line.endswith(":"):
                pattern = line.strip().strip(":")
                base_dir = os.path.split(pattern)[0]
                g = glob.glob(os.path.join(base, pattern))
                if len(g) == 0:
                    print("Warning: Pattern '%s' matches 0 files." % pattern)
                results += [(base_dir, x) for x in g]
    return results


def copy_manifest(output_dir, manifest_file, manifest_base, target):
    """
    Given a manifest file "manifest_file" and a base directory "manifest_base"
    used as the source of the filenames listed in the manifest, copy the
    files into a subdirectory "target" of "output_dir".

    Returns the manifest when done.
    """
    manifest_dest = os.path.join(output_dir, target)
    os.mkdir(manifest_dest)
    dir_src = os.path.join(args.repository, manifest_base)
    all_files = read_manifest(manifest_file, dir_src)
    for (b, i) in sorted(all_files):
        mkdir_p(os.path.join(manifest_dest, b))
        src = os.path.join(dir_src, i)
        dst = os.path.join(manifest_dest, b, os.path.split(i)[1])
        if os.path.isdir(src):
            shutil.copytree(src, dst, symlinks=True)
        else:
            shutil.copyfile(src, dst)
    return all_files


# Check usage.
parser = argparse.ArgumentParser(
    description='Generate autocorres release tarball.')
parser.add_argument('version', metavar='VERSION',
                    type=str, help='Version number of the release, such as "0.95-beta1".')
parser.add_argument('cparser_tar', metavar='CPARSER_RELEASE',
                    type=str, help='Tarball to the C parser release.')
parser.add_argument('isabelle_bin', metavar='ISABELLE_BIN',
                    type=str, help='path to Isabelle release binary, e.g ~/Isabelle2021/bin/isabelle')
parser.add_argument('-b', '--browse', action='store_true',
                    help='Open shell to browse output prior to tar\'ing.')
parser.add_argument('-o', '--output', metavar='FILENAME',
                    default=None, help='Output filename. Defaults to "autocorres-<VERSION>.tar.gz".')
parser.add_argument('--dry-run', action='store_true',
                    help='Do not output any files.', default=False)
parser.add_argument('-t', '--test', action='store_true', default=False,
                    help='Test the archive.')
parser.add_argument('--no-cleanup', action='store_true',
                    help='Don''t delete temporary directories.', default=False)
parser.add_argument('-r', '--repository', metavar='REPO',
                    type=str, help='Path to the L4.verified repository base.', default=None)
parser.add_argument('--archs', metavar='ARCH,...',
                    type=str, default='ARM,ARM_HYP,X64,RISCV64,AARCH64',
                    help='L4V_ARCHs to include (comma-separated)')
args = parser.parse_args()

args.archs = args.archs.split(',')

# Setup output filename if the user used the default.
if args.output is None:
    args.output = "autocorres-%s.tar.gz" % args.version

# If no repository was specified, assume it is in the cwd.
if args.repository is None:
    try:
        args.repository = subprocess.check_output([
            "git", "rev-parse", "--show-toplevel"]).strip()
    except subprocess.CalledProcessError:
        parser.error("Could not determine repository location.")

# Get absolute paths to files.
args.repository = os.path.abspath(args.repository).decode("utf-8")
if not args.dry_run:
    args.output = os.path.abspath(args.output)
else:
    args.output = None
release_files_dir = os.path.join(args.repository, "tools", "autocorres", "tools", "release_files")

# Ensure C-parser exists, and looks like a tarball.
if not os.path.exists(args.cparser_tar) or not args.cparser_tar.endswith(".tar.gz"):
    parser.error("Expected a path to the C parser release tarball.")
args.cparser_tar = os.path.abspath(args.cparser_tar)

# Ensure Isabelle release exists
if not os.path.exists(args.isabelle_bin):
    parser.error("Expected a path to the official Isabelle release binary.")
args.isabelle_bin = os.path.abspath(args.isabelle_bin)
base_isabelle_bin = args.isabelle_bin

# Tools for theory dependencies.
thydeps_tool = os.path.join(args.repository, 'misc', 'scripts', 'thydeps')
repo_isabelle_dir = os.path.join(args.repository, 'isabelle')

# User's preferred shell, if any.
user_shell = os.environ.get('SHELL', '/bin/sh')

# Create temp dir.
with TempDir(cleanup=(not args.no_cleanup)) as base_dir:
    # Generate base directory.
    target_dir_name = "autocorres-%s" % args.version
    target_dir = os.path.join(base_dir, target_dir_name)
    os.mkdir(target_dir)

    # Copy autocorres files.
    print("Copying files...")
    ac_files = copy_manifest(target_dir,
                             os.path.join(release_files_dir, "AUTOCORRES_FILES"),
                             os.path.join(args.repository, "tools", "autocorres"), "autocorres")

    # Copy theories from dependent sessions in the lib directory.
    lib_deps = ''
    for arch in args.archs:
        print(f"Getting dependencies for {arch}")
        lib_deps += subprocess.check_output(
            [thydeps_tool, '-I', repo_isabelle_dir, '-d', '.', '-d', 'tools/autocorres/tests',
             '-b', 'lib', '-r',
             'AutoCorresTest'],
            cwd=args.repository, env=dict(os.environ, L4V_ARCH=arch)).decode("utf-8")
    lib_deps = sorted(set(lib_deps.splitlines()))

    for f in lib_deps:
        f_src = os.path.join(args.repository, 'lib', f)
        f_dest = os.path.join(target_dir, 'lib', f)
        mkdir_p(os.path.dirname(f_dest))
        shutil.copyfile(f_src, f_dest)

    # Copy various other files.
    for session in ['Basics', 'Eisbach_Tools', 'ML_Utils', 'Monads', 'Word_Lib']:
        shutil.copyfile(
            os.path.join(args.repository, 'lib', session, 'ROOT'),
            os.path.join(target_dir, 'lib', session, 'ROOT'))
    shutil.copyfile(
        os.path.join(release_files_dir, "ROOT.release"),
        os.path.join(target_dir, "autocorres", "ROOT"))
    shutil.copyfile(
        os.path.join(release_files_dir, "ROOTS.base_dir"),
        os.path.join(target_dir, "ROOTS"))
    for i in ["README", "ChangeLog"]:
        shutil.copyfile(
            os.path.join(release_files_dir, i),
            os.path.join(target_dir, i))
    shutil.copyfile(
        os.path.join(release_files_dir, "CONTRIBUTORS"),
        os.path.join(target_dir, "autocorres", "CONTRIBUTORS"))

    # License files.
    shutil.copytree(
        os.path.join(args.repository, "LICENSES"),
        os.path.join(target_dir, "LICENSES"))

    # Set up ROOT for the tests dir, for the thydeps tool
    subprocess.check_call(
        ['make', 'tests/ROOT'],
        cwd=os.path.join(args.repository, 'tools', 'autocorres'))

    # For the examples, generate ".thy" files where appropriate, and also
    # generate an "All.thy" which contains all the examples.
    def gen_thy_file(c_file):
        thy_file = os.path.splitext(c_file)[0] + ".thy"
        base_name = os.path.splitext(os.path.basename(c_file))[0]
        with open(thy_file, "w") as f:
            f.write('''
theory %s
imports
  "AutoCorres.AutoCorres"
begin

install_C_file "%s"

autocorres "%s"

end
            '''.strip() % (base_name,
                           os.path.basename(c_file),
                           os.path.basename(c_file)
                           ))

    for f in glob.glob(os.path.join(target_dir, "autocorres", "tests", "parse-tests", "*.c")):
        gen_thy_file(f)
    subprocess.check_call([
        "python",
        os.path.join(args.repository, "misc", "scripts", "gen_isabelle_root.py"),
        "-T", "-o", os.path.join(target_dir, "autocorres", "tests", "AutoCorresTest.thy"),
        "-i", os.path.join(target_dir, "autocorres", "tests", "parse-tests"),
        "-i", os.path.join(target_dir, "autocorres", "tests", "proof-tests"),
        "-i", os.path.join(target_dir, "autocorres", "tests", "examples"),
    ])

    # Update include paths: change "../../lib" to "../lib".
    def inplace_replace_string(filename, old_string, new_string):
        with open(filename) as f:
            data = f.read()
        new_data = data.replace(old_string, new_string)
        if new_data != data:
            print('    replaced ../../lib with ../lib in %r' % filename)
        with open(filename, "w") as f:
            f.write(new_data)
    for f in rglob(os.path.join(target_dir, "autocorres"), "*.thy"):
        inplace_replace_string(f, "../../lib/", "../lib/")

    # Extract the C parser
    print("Extracting C parser...")
    # We want to mix the C parser directory structure around a little.
    with TempDir() as c_parser_working_dir:
        subprocess.check_call(["tar", "-xz", "-C", c_parser_working_dir,
                               "--strip-components=1", "-f", args.cparser_tar])
        # The C parser uses mllex and mlyacc to generate its grammar. We build
        # the grammar files so that our release won't have a dependency on mlton.
        print("Generating C parser grammar files...")
        subprocess.check_call(['make', 'c-parser-deps'],
                              cwd=os.path.join(c_parser_working_dir, "src", "c-parser"))
        shutil.move(os.path.join(c_parser_working_dir, "src", "c-parser"),
                    os.path.join(target_dir, "c-parser"))
        shutil.move(os.path.join(c_parser_working_dir, "README.md"),
                    os.path.join(target_dir, "c-parser", "README.md"))
        shutil.move(os.path.join(c_parser_working_dir, "doc", "ctranslation.pdf"),
                    os.path.join(target_dir, "c-parser", "doc", "ctranslation.pdf"))

    # Double-check our theory dependencies.
    if os.path.exists(thydeps_tool):
        print("Checking theory dependencies...")
        thy_deps = ''
        for arch in args.archs:
            thy_deps += subprocess.check_output(
                [thydeps_tool, '-I', repo_isabelle_dir, '-b', '.', '-r',
                 'AutoCorres', 'AutoCorresTest'],
                cwd=target_dir, env=dict(os.environ, L4V_ARCH=arch)).decode("utf-8")
        thy_deps = sorted(set(thy_deps.splitlines()))
        needed_files = [os.path.join(args.repository, f)
                        for f in thy_deps
                        if f.startswith('tools/autocorres')]

        manifest_files = [os.path.join(dir, file) for dir, file in ac_files]
        missing_files = [f for f in needed_files if f not in manifest_files]
        if missing_files:
            print("Warning: missing dependencies from release manifest:")
            for f in missing_files:
                print("  - %s" % f)
    else:
        print("Warning: cannot check theory dependencies: missing tool %r" % thydeps_tool)

    # Check for bad strings.
    print("Searching for bad strings...")
    for s in ["davidg", "dgreenaway", "jlim", "jalim", "autorefine"]:
        ret = subprocess.call(["grep", "-i", "-r", s, base_dir])
        if not ret:
            raise Exception("Found a bad string")

    # Set modified date of everything.
    print("Setting file modification/access dates...")
    target_time = int(time.mktime(time.localtime()))
    for (root, dirs, files) in os.walk(base_dir, followlinks=False):
        for i in dirs + files:
            os.utime(os.path.join(root, i), (target_time, target_time))

    # Build the documentation.
    def build_docs(tree, isabelle_bin):
        with TempDir() as doc_build_dir:
            # Make a copy of the directory, so we don't pollute it.
            shutil.copytree(tree, os.path.join(doc_build_dir, "doc"), symlinks=True)

            # Build the docs.
            try:
                subprocess.check_call(
                    [isabelle_bin, "build", "-c", "-d", ".", "-d",
                        "./autocorres/doc/quickstart", "-v", "AutoCorresQuickstart"],
                    cwd=os.path.join(doc_build_dir, "doc"), env=dict(os.environ, L4V_ARCH="ARM"))
            except subprocess.CalledProcessError:
                print("Building documentation failed.")
                if args.browse:
                    subprocess.call(user_shell, cwd=target_dir)

            # Copy the generated PDF into our output.
            shutil.copyfile(
                os.path.join(doc_build_dir, "doc", "autocorres", "doc",
                             "quickstart", "output", "document.pdf"),
                os.path.join(tree, "quickstart.pdf"))
    print("Building documentation...")
    build_docs(target_dir, base_isabelle_bin)

    # Compress everything up.
    if args.output != None:
        print("Creating tarball...")
        tar = 'gtar' if sys.platform == "darwin" else 'tar'
        subprocess.check_call([tar, "-cz", "--numeric-owner",
                               "--owner", "nobody", "--group", "nogroup",
                               "-C", base_dir, "-f", args.output, target_dir_name])

    # Run a test if requested.
    if args.test:
        print("Testing release...")
        try:
            subprocess.check_call([base_isabelle_bin, "version"], cwd=target_dir)
            for arch in args.archs:
                subprocess.check_call([base_isabelle_bin, "build", "-d", ".", "-v",
                                       "AutoCorres", "AutoCorresTest"],
                                      cwd=target_dir, env=dict(os.environ, L4V_ARCH=arch))
        except subprocess.CalledProcessError:
            print("Test failed")
            if args.browse:
                subprocess.call(user_shell, cwd=target_dir)

    # Open a shell in the directory if requested.
    if args.browse:
        print("Opening shell...")
        subprocess.call(user_shell, cwd=target_dir)
