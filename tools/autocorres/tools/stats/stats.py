#!/usr/bin/env python
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import os
import errno
import subprocess
import argparse
import shutil
import tempfile
import datetime
import glob
import time
import re
import numpy

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


def mkdir_p(path):
    try:
        os.makedirs(path)
    except OSError as exc:
        if exc.errno == errno.EEXIST:
            pass
        else:
            raise


def phase_sort_key(x):
    d = {
        "CParser": 1,
        "L1": 2,
        "L1except": 3,
        "L1peep": 4,
        "L2": 5,
        "L2simp": 6,
        "HL": 7,
        "HLsimp": 8,
        "TS": 9,
        "polish": 10,
    }
    if x in d:
        return (d[x], x)
    return (100, x)


def write_theory_file(f, enable_stats):
    f.write("""
        theory Stats
        imports AutoCorres
        begin

        (* %(time)s *)

        declare [[record_codegen = false]]
        declare [[allow_underscore_idents = true]]

        (* Start recording times. *)
        ML {*
            val cpuTimer = Timer.startCPUTimer ();
            val realTimer = Timer.startRealTimer ();
        *}

        (* Parse the C file. *)
        install_C_file "input.c"

        (* Fetch C parser times. *)
        ML {*
            val {sys = a, usr = b} = Timer.checkCPUTimer cpuTimer;
            writeln ("C Parser CPU Time : " ^ (PolyML.makestring (Time.toMilliseconds a + Time.toMilliseconds b)));
            writeln ("C Parser Real Time : " ^ (PolyML.makestring (Timer.checkRealTimer realTimer |> Time.toMilliseconds)));

            val cpuTimer = Timer.startCPUTimer ();
            val realTimer = Timer.startRealTimer ();
        *}

        (* Enable statistics. *)
        ML {* if %(enable_stats)s then Statistics.setup_measure_fn (Statistics.complexity_measure_fn) else () *}

        autocorres "input.c"

        (* Fetch autocorres times. *)
        ML {*
            val {sys = a, usr = b} = Timer.checkCPUTimer cpuTimer;
            writeln ("AutoCorres CPU Time : " ^ (PolyML.makestring (Time.toMilliseconds a + Time.toMilliseconds b)));
            writeln ("AutoCorres Real Time : " ^ (PolyML.makestring (Timer.checkRealTimer realTimer |> Time.toMilliseconds)));
        *}

        end
        """ % {
            "time": str(datetime.datetime.now()),
            "enable_stats": "true" if enable_stats else "false",
            })


# Check usage.
parser = argparse.ArgumentParser(
    description='Generate statistics about AutoCorres and the C Parser.')
parser.add_argument('input', metavar='INPUT',
                    type=str, help='Input C source file.')
parser.add_argument('-n', '--no-isabelle',
                    default=False, action='store_true',
                    help="Don't run Isabelle, but reuse previous log file.")
parser.add_argument('-b', '--browse', default=False, action='store_true',
                    help='Open shell in temp directory.')
parser.add_argument('-r', '--root', action='store', type=str,
                    help='Root to l4.verified directory.', default=None)
parser.add_argument('-R', '--repeats', action='store',
                    help='Number of runs for timing data.', default=1)
parser.add_argument('-o', '--output', metavar='OUTPUT',
                    default="/dev/stdout", type=str, help='Output file.')
args = parser.parse_args()

if args.root == None and not args.no_isabelle:
    parser.error("Must specify root to l4.verified directory.")
if args.root != None:
    args.root = os.path.abspath(args.root)

output = open(args.output, "w")
output.write("Processing %s\n\n" % args.output)

# Create temp dir.
with TempDir() as tmp_dir:
    try:
        # Copy file.
        shutil.copyfile(args.input, os.path.join(tmp_dir, "input.c"))

        # Get lines of code.
        lines_of_code = int(subprocess.check_output(
            ["c_count", args.input]).strip().split("\n")[-1])

        # Generate a root file.
        with open(os.path.join(tmp_dir, "ROOT"), "w") as f:
            f.write("""
                session Stats = AutoCorres +
                  theories
                    "Stats"
                """)

        #
        # Pass 1: Generate statisics.
        #

        # Generate a theory file.
        with open(os.path.join(tmp_dir, "Stats.thy"), "w") as f:
            write_theory_file(f, enable_stats=True)

        # Process theory file with Isabelle.
        if not args.no_isabelle:
            subprocess.check_call(["isabelle", "build", "-v", "-d", args.root,
                                   "-d", ".", "-c", "Stats"], cwd=tmp_dir)

        # Fetch log file.
        log_data = subprocess.check_output(
            ["isabelle", "env", "sh", "-c", "zcat ${ISABELLE_OUTPUT}/log/Stats.gz"])
        phase_lines_of_spec = {}
        phase_term_size = {}
        phase_num_functions = {}
        num_functions = 0
        for line in log_data.replace("\r", "").split("\n"):
            if line.startswith("Defining (L1)"):
                num_functions += 1
            if line.startswith("SC"):
                m = re.match("^SC: ([A-Za-z0-9]+): ([^ ]+) (\d+) LoS: (\d+)$", line)
                if m:
                    phase = m.group(1)
                    term_size = m.group(3)
                    los = m.group(4)

                    for d in [phase_lines_of_spec, phase_term_size, phase_num_functions]:
                        d.setdefault(m.group(1), 0)

                    phase_num_functions[phase] += 1
                    phase_term_size[phase] += int(term_size)
                    phase_lines_of_spec[phase] += int(los)

        output.write("\n")
        output.write("%d input line(s) of code\n" % lines_of_code)
        output.write("%d function(s)\n" % num_functions)
        output.write("\n")
        output.write("%-10s %10s %10s\n" % ("Phase", "LoS", "Term Size"))

        for phase in sorted(phase_term_size.keys(), key=phase_sort_key):
            output.write("%-10s %10d %10d\n" % (phase,
                                                phase_lines_of_spec[phase], phase_term_size[phase] / phase_num_functions[phase]))
        output.write("\n")

        #
        # Pass 2: generate timing data.
        #

        # Generate a theory file.
        with open(os.path.join(tmp_dir, "Stats.thy"), "w") as f:
            write_theory_file(f, enable_stats=False)

        # Process theory file with Isabelle.
        c_parser_cpu_time = []
        c_parser_real_time = []
        ac_cpu_time = []
        ac_real_time = []
        for i in xrange(int(args.repeats)):
            if not args.no_isabelle:
                subprocess.check_call(["isabelle", "build", "-v", "-o", "threads=1",
                                       "-d", args.root, "-d", ".", "-c", "Stats"], cwd=tmp_dir)

            # Fetch log file.
            log_data = subprocess.check_output(
                ["isabelle", "env", "sh", "-c", "zcat ${ISABELLE_OUTPUT}/log/Stats.gz"])
            for line in log_data.replace("\r", "").split("\n"):
                if line.startswith("C Parser CPU Time"):
                    c_parser_cpu_time.append(int(line.split(":")[1]))
                if line.startswith("C Parser Real Time"):
                    c_parser_real_time.append(int(line.split(":")[1]))
                if line.startswith("AutoCorres CPU Time"):
                    ac_cpu_time.append(int(line.split(":")[1]))
                if line.startswith("AutoCorres Real Time"):
                    ac_real_time.append(int(line.split(":")[1]))

        # Generate summary data.
        for (name, values) in [
                ("C Parser CPU Time", c_parser_cpu_time),
                ("C Parser Real Time", c_parser_real_time),
                ("AutoCorres CPU Time", ac_cpu_time),
                ("AutoCorres Real Time", ac_real_time),
        ]:
            output.write("%s: %.2f (%.2f)\n" % (name, numpy.mean(values), numpy.std(values)))
            output.write("    samples: " + (", ".join([str(x) for x in values])) + "\n")

        # Open a shell in the directory if requested.
        if args.browse:
            print "Opening shell..."
            subprocess.call("zsh", cwd=tmp_dir)
    except Exception as e:
        print "Test failed"
        print e
        if args.browse:
            subprocess.call("zsh", cwd=tmp_dir)
        raise
