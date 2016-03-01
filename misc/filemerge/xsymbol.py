#!/usr/bin/env python
# This Python file uses the following encoding: utf-8
#
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
#  xsymbol.py
#
#  Author: Andrew Boyton, NICTA
#  Based on code by Timothy Bourke, NICTA
#

from __future__ import print_function
import os, sys

# Make isasymbols importable.
sys.path.append(os.path.join(os.path.dirname(__file__), '../pysymbols'))
import isasymbols

translator = isasymbols.make_translator(os.path.join(os.path.dirname(__file__),
    '../../isabelle/etc/symbols'))

if len(sys.argv) > 1:
    f = open(sys.argv[1], 'r')
else:
    f = sys.stdin

data = f.read()
print(translator.encode(data).encode('utf-8'), end='')
