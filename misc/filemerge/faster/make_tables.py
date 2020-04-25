#!/usr/bin/env python
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import isasymbols
import argparse
import os
import sys

MY_DIR = os.path.dirname(os.path.abspath(__file__))

sys.path.append(os.path.join(MY_DIR, '../../../internal/misc/pysymbols'))


def main(argv):
    parser = argparse.ArgumentParser(
        description='generate unicode-ascii translation tables')
    parser.add_argument('--output', '-o', type=argparse.FileType('w'),
                        default=sys.stdout, help='output file')
    options = parser.parse_args(argv[1:])

    with open(os.path.join(MY_DIR, '../../../isabelle/etc/symbols')) as f:
        t = isasymbols.Translator(f.read())

    # Write an ASCII-to-unicode table.
    options.output.write('static map<wstring, wchar_t> ascii_to_unicode = {\n')
    for sym in t.symbols:
        options.output.write('    { L"%s", L\'\\x%x\' },\n' %
                             (sym.ascii_text.replace('\\', '\\\\'), sym.code_point))
    options.output.write('};\n\n')

    # Write a unicode-to-ASCII table.
    options.output.write('static map<wchar_t, wstring> unicode_to_ascii = {\n')
    for s in t.symbols:
        options.output.write('    { L\'\\x%x\', L"%s" },\n' %
                             (s.code_point, s.ascii_text.replace('\\', '\\\\')))
    options.output.write('};\n\n')

    # Work out the maximum length of an ASCII sequence.
    ascii_seq_max = max(len(s.ascii_text) for s in t.symbols)
    options.output.write('static const unsigned int ASCII_SEQ_MAX = %u;\n\n' %
                         ascii_seq_max)

    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
