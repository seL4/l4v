#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
Basic functionality for constructing apply-style proofs from Python.

Example usage:

    p = Proof('True \\<and> True')
    p.apply('rule conjI', solves=-1)
    p.apply('simp')
    p.apply('simp')
    p.done()
    print(p)
'''

import StringIO
from .exception import IsaSymbolsException


class Proof(object):
    def __init__(self, statement, name=None, debug=True):
        self.statement = statement
        self.name = name
        self.steps = []
        self.subgoals = 1
        self.completed = None
        self.debug = debug

    def apply(self, step, solves=0):
        if self.completed:
            raise IsaSymbolsException('you cannot apply steps to a completed '
                                      'proof')
        if solves > self.subgoals:
            raise IsaSymbolsException('you cannot solve more subgoals (%d) '
                                      'than remain (%d)' % (solves, self.subgoals))
        if ' ' in step:
            step = '(%s)' % step
        self.steps.append((' ' * (self.subgoals - 1), step))
        self.subgoals -= solves

    def done(self):
        if self.subgoals > 0:
            raise IsaSymbolsException('%d subgoals remain' % self.subgoals)
        if self.completed is not None:
            raise IsaSymbolsException('proof already completed')
        self.completed = 'done'

    def oops(self):
        if self.completed is not None:
            raise IsaSymbolsException('proof already completed')
        self.completed = 'oops'

    def sorry(self):
        if self.completed:
            raise IsaSymbolsException('proof already completed')
        self.completed = 'sorry'

    def __repr__(self):
        s = StringIO.StringIO()
        s.write('lemma ')
        if self.name is not None:
            s.write('%s:' % self.name)
        s.write('"%s"\n' % self.statement)
        if not self.debug and self.completed == 'done':
            # Write the lemma out as a monolithic `by` statement to maximise
            # parallelism.
            s.write('  by (%s)' % ',\n      '.join(
                '%s%s' % (indent, step) for indent, step in self.steps))
        else:
            if len(self.steps) > 0:
                s.write('\n'.join(
                    '  %sapply %s' % (indent, step) for indent, step in self.steps))
                if self.completed is not None:
                    s.write('\n')
            if self.completed is not None:
                if self.subgoals == 0:
                    s.write('  %s' % self.completed)
                else:
                    s.write('  %s%s' % (' ' * (self.subgoals - 1), self.completed))
        return s.getvalue()
