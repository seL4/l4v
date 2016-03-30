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

import os
import errno
import subprocess
import argparse
import shutil
import tempfile
import glob
import time
import fnmatch

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
        for line in f.xreadlines():
            line = line.strip("\r\n")
            if not line.startswith(" ") and line.endswith(":"):
                pattern = line.strip().strip(":")
                base_dir = os.path.split(pattern)[0]
                g = glob.glob(os.path.join(base, pattern))
                if len(g) == 0:
                    print ("Warning: Pattern '%s' matches 0 files." % pattern)
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
parser.add_argument('isabelle_tar', metavar='ISABELLE_TARBALL',
        type=str, help='Tarball to the official Isabelle release')
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
args = parser.parse_args()

# Setup output filename if the user used the default.
if args.output == None:
    args.output = "autocorres-%s.tar.gz" % args.version

# If no repository was specified, assume it is in the cwd.
if args.repository == None:
    try:
        args.repository = subprocess.check_output([
            "git", "rev-parse", "--show-toplevel"]).strip()
    except subprocess.CalledProcessError:
        parser.error("Could not determine repository location.")

# Get absolute paths to files.
args.repository = os.path.abspath(args.repository)
if not args.dry_run:
    args.output = os.path.abspath(args.output)
else:
    args.output = None
release_files_dir = os.path.join(args.repository, "tools", "autocorres", "tools", "release_files")

# Ensure C-parser exists, and looks like a tarball.
if not os.path.exists(args.cparser_tar) or not args.cparser_tar.endswith(".tar.gz"):
    parser.error("Expected a path to the C parser release tarball.")
args.cparser_tar = os.path.abspath(args.cparser_tar)

# Ensure Isabelle exists, and looks like a tarball.
if not os.path.exists(args.isabelle_tar) or not args.isabelle_tar.endswith(".tar.gz"):
    parser.error("Expected a path to the official Isabelle release.")
args.isabelle_tar = os.path.abspath(args.isabelle_tar)

# Create temp dir.
with TempDir(cleanup=(not args.no_cleanup)) as base_dir:
    # Generate base directory.
    target_dir_name = "autocorres-%s" % args.version
    target_dir = os.path.join(base_dir, target_dir_name)
    os.mkdir(target_dir)

    # Copy autocorres files.
    print "Copying files..."
    ac_files = copy_manifest(target_dir,
                             os.path.join(release_files_dir, "AUTOCORRES_FILES"),
                             os.path.join(args.repository, "tools", "autocorres"), "autocorres")

    # Copy lib files.
    lib_files = copy_manifest(target_dir,
                              os.path.join(release_files_dir, "LIB_FILES"),
                              os.path.join(args.repository, "lib"), "lib")

    # Double-check our theory dependencies.
    thydeps_tool = os.path.join(args.repository, 'misc/scripts/thydeps')
    if os.path.exists(thydeps_tool):
        print "Checking theory dependencies..."
        included_thys = [os.path.join(dir, file)
                         for dir, file in lib_files if file.endswith('.thy')]
        included_thys += [os.path.join(dir, file)
                          for dir, file in ac_files if file.endswith('.thy')]
        thy_deps = subprocess.check_output([thydeps_tool, '-T', 'text', '-o', '-'] + included_thys,
                                           cwd=args.repository)
        thy_deps = thy_deps.splitlines()
        needed_files = [os.path.join(args.repository, f)
                        for f in thy_deps if f.startswith('lib') or f.startswith('tools/autocorres')]

        manifest_files = [os.path.join(dir, file) for dir, file in ac_files + lib_files]
        missing_files = [f for f in needed_files if f not in manifest_files]
        if missing_files:
            print "Warning: missing dependencies from release manifest:"
            for f in missing_files:
                print("  - %s" % f)
    else:
        print "Warning: cannot check theory dependencies: missing tool misc/scripts/thydeps"

    # Copy various other files.
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
    shutil.copyfile(
            os.path.join(args.repository, "LICENSE_BSD2.txt"),
            os.path.join(target_dir, "LICENSE_BSD2.txt"))

    # For the examples, generate ".thy" files where appropriate, and also
    # generate an "All.thy" which contains all the examples.
    def gen_thy_file(c_file):
        thy_file = os.path.splitext(c_file)[0] + ".thy"
        base_name = os.path.splitext(os.path.basename(c_file))[0]
        with open(thy_file, "w") as f:
            f.write('theory %s\n' % base_name)
            f.write('imports "../../AutoCorres"\n')
            f.write('begin\n\n')
            f.write('install_C_file "%s"\n\n' % os.path.basename(c_file))
            f.write('autocorres "%s"\n\n' % os.path.basename(c_file))
            f.write('end\n')
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
        with open(filename, "w") as f:
            f.write(new_data)
    for f in rglob(os.path.join(target_dir, "autocorres"), "*.thy"):
        inplace_replace_string(f, "../../lib", "../lib")

    ## Check licenses
    #print "Checking licenses..."
    #subprocess.check_call([
    #    os.path.join(args.repository, "misc", "license-tool", "check_license.py"),
    #    "--exclude", os.path.join(release_files_dir, "licenses-ignore"),
    #    os.path.join(target_dir)])

    ## Expand licenses.
    #print "Expanding licenses..."
    #subprocess.check_call([
    #    os.path.join(args.repository, "misc", "license-tool", "expand_license.py"),
    #    os.path.join(release_files_dir, "licenses"),
    #    os.path.join(target_dir)])

    # Extract the C parser
    print "Extracting C parser..."
    # We want to mix the C parser directory structure around a little.
    with TempDir() as c_parser_working_dir:
        subprocess.check_call(["tar", "-xz", "-C", c_parser_working_dir, "--strip-components=1", "-f", args.cparser_tar])
        shutil.move(os.path.join(c_parser_working_dir, "src", "c-parser"), os.path.join(target_dir, "c-parser"))
        shutil.move(os.path.join(c_parser_working_dir, "README"), os.path.join(target_dir, "c-parser", "README"))
        shutil.move(os.path.join(c_parser_working_dir, "doc", "ctranslation.pdf"), os.path.join(target_dir, "c-parser", "doc", "ctranslation.pdf"))

    # Patch the release.
    def do_patch(patch_file):
        subprocess.check_call(["patch", "-p", "1", "-r", "-", "--no-backup-if-mismatch", "--quiet",
            "-i", patch_file], cwd=target_dir)
    for i in sorted(glob.glob(os.path.join(release_files_dir, "*.patch"))):
        do_patch(i)

    # Check for bad strings.
    print "Searching for bad strings..."
    for s in ["davidg", "dgreenaway", "jlim", "jalim", "autorefine", "@LICENSE"]:
        ret = subprocess.call(["grep", "-i", "-r", s, base_dir])
        if not ret:
            raise Exception("Found a bad string")

    # Set modified date of everything.
    print "Setting file modification/access dates..."
    target_time = int(time.mktime(time.localtime()))
    for (root, dirs, files) in os.walk(base_dir, followlinks=False):
        for i in dirs + files:
            os.utime(os.path.join(root, i), (target_time, target_time))

    # Extract the Isabelle release
    print "Extracting Isabelle..."
    isabelle_dir = os.path.join(base_dir, "isabelle")
    mkdir_p(isabelle_dir)
    subprocess.check_call(["tar", "-xz", "-C", isabelle_dir, "--strip-components=1", "-f", args.isabelle_tar])
    isabelle_bin = os.path.join(isabelle_dir, "bin", "isabelle")
    assert os.path.exists(isabelle_bin)

    # Build the documentation.
    def build_docs(tree, isabelle_bin):
        with TempDir() as doc_build_dir:
            # Make a copy of the directory, so we don't pollute it.
            shutil.copytree(tree, os.path.join(doc_build_dir, "doc"), symlinks=True)

            # Build the docs.
            try:
                subprocess.check_call([
                        isabelle_bin, "build", "-c", "-d", ".",
                                "-d", "./autocorres/doc/quickstart",
                                "AutoCorresQuickstart"],
                        cwd=os.path.join(doc_build_dir, "doc"))
            except subprocess.CalledProcessError:
                print "Building documentation failed."
                if args.browse:
                    subprocess.call("zsh", cwd=target_dir)

            # Copy the generated PDF into our output.
            shutil.copyfile(
                    os.path.join(doc_build_dir, "doc", "autocorres", "doc", "quickstart", "output", "document.pdf"),
                    os.path.join(tree, "quickstart.pdf"))
    print "Building documentation..."
    build_docs(target_dir, isabelle_bin)

    # Compress everything up.
    if args.output != None:
        print "Creating tarball..."
        subprocess.check_call(["tar", "-cz", "--numeric-owner",
            "--owner", "root", "--group", "root",
            "-C", base_dir, "-f", args.output, target_dir_name])

    # Run a test if requested.
    if args.test:
        print "Testing release..."
        try:
            subprocess.check_call([isabelle_bin, "version"], cwd=target_dir)
            subprocess.check_call([isabelle_bin, "build", "-d", ".", "AutoCorres", "AutoCorresTest"], cwd=target_dir)
        except subprocess.CalledProcessError:
            print "Test failed"
            if args.browse:
                subprocess.call("zsh", cwd=target_dir)

    # Open a shell in the directory if requested.
    if args.browse:
        print "Opening shell..."
        subprocess.call("zsh", cwd=target_dir)

