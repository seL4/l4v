#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#
"""Parser for skeletons of theory files which are completed
by inserting parsed Haskell."""

from __future__ import print_function
from __future__ import absolute_import
import sys
import lhs_pars
import os
import os.path


def create_find_source():
    dir = os.environ['L4CAP']
    dir = os.path.join(dir, 'src')
    return lambda x: os.path.join(dir, x)


find_source = create_find_source()


def actual_fn(d):
    return d.get('actual_fn', d['defined'])


if sys.argv[1] == '-q':
    instructions = open(sys.argv[2])
    quiet = True
else:
    instructions = open(sys.argv[1])
    quiet = False

for line in instructions:
    instruct = line.strip()
    if not instruct:
        continue

    [input, output] = [bit.strip() for bit in instruct.split('-->')]
    output_tmp = os.path.join(os.path.dirname(output), 'pars_skel.tmp')

    output_f = open(output_tmp, 'w')

    input_f = open(input)
    for line in input_f:
        if line.startswith('#INCLUDE_HASKELL'):
            call = lhs_pars.Call()

            bits = line.split()

            call.filename = find_source(bits[1])
            call.all_bits = 'all_bits' in bits
            call.decls_only = 'decls_only' in bits
            call.instanceproofs = 'instanceproofs' in bits
            call.bodies_only = 'bodies_only' in bits
            call.moduletranslations = dict([bit.split('=')
                                            for bit in bits if '=' in bit])
            call.body = 'BODY' in bits
            if 'defsincludingarch' in bits:
                call.decls_only = True
                call.archdefs = True
            if 'ONLY' in bits:
                n = bits.index('ONLY')
                m = dict([(name, 1) for name in bits[n + 1:]])
                call.restr = lambda x: x['defined'] in m
            if 'NOT' in bits:
                n = bits.index('NOT')
                m = dict([(name, 1) for name in bits[n + 1:]])
                call.restr = lambda x: not x['defined'] in m
            if 'NOTBODY' in bits:
                n = [i for (i, s) in enumerate(bits) if s == 'NOTBODY']
                l = [bits[i + 1] for i in n]
                M = dict([(name, 1) for name in l])
                prev = call.restr
                if prev:

                    def restr(x):
                        if actual_fn(x) in M:
                            return False
                        else:
                            return prev(x)
                else:
                    restr = lambda x: actual_fn(x) not in M
                call.restr = restr
            if call.body:
                assert bits[-2] == 'BODY'
                fn = bits[-1]
                call.restr = lambda x: actual_fn(x) == fn

            try:
                parsed = lhs_pars.parse(call)
            except:
                print("%s -X-> %s" % (input, output))
                raise

            if bits[0] == '#INCLUDE_HASKELL_PREPARSE':
                pass
            else:
                output_f.writelines(parsed)
        else:
            output_f.write(line)

    output_f.close()

    try:
        lines1 = [line for line in open(output_tmp)]
        lines2 = [line for line in open(output)]

        changed = not (lines1 == lines2)
    except:
        changed = 1
    if changed:
        if not quiet:
            print(instruct)
        try:
            os.unlink(output)
        except:
            pass
        os.rename(output_tmp, output)
    else:
        os.unlink(output_tmp)

lhs_pars.warn_supplied_usage()
