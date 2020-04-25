#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

#  xsymbol.py
#
#  Author: Andrew Boyton, NICTA
#  Based on code by Timothy Bourke, NICTA
#

import isasymbols
from __future__ import print_function
import os
import sys

# Make isasymbols importable.
sys.path.append(os.path.join(os.path.dirname(__file__), '../pysymbols'))

translator = isasymbols.make_translator(os.path.join(os.path.dirname(__file__),
                                                     '../../isabelle/etc/symbols'))

if len(sys.argv) > 1:
    f = open(sys.argv[1], 'r')
else:
    f = sys.stdin

data = f.read()
print(translator.encode(data).encode('utf-8'), end='')
