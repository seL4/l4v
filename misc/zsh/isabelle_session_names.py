#!python
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import sys
import re


def strip_comments(s):
    s2 = ''
    d = 0
    quote = False
    i, l = 0, len(s)
    while i < l:
        if quote == False and s[i:i+2] == '(*':
            d += 1
            i += 2
        elif quote == False and s[i:i+2] == '*)' and d > 0:
            d -= 1
            i += 2
        else:
            if d == 0:
                s2 += s[i]
                if quote == s[i]:
                    quote = False
                elif s[i] in ['"', "'"]:
                    quote = s[i]
            i += 1
    return s2


def unquote(s):
    if s[:1] == '"' and s[-1:] == '"':
        return s[1:-1]
    return s


def get(dir):
    sessions = []
    try:
        root = strip_comments(''.join(open(dir + '/ROOT').readlines()))
        sessions += [unquote(s) for s in re.findall('session\s+("[^"]*"|\S+)', root)]
    except IOError:
        pass
    try:
        roots = [l.strip() for l in open(dir + '/ROOTS').readlines() if l.strip()[:1] != '#']
        for dir2 in roots:
            sessions += get(dir + '/' + dir2)
    except IOError:
        pass
    return sessions


if '-h' in sys.argv or '--help' in sys.argv:
    print('Usage: %s DIRS...' % sys.argv[0])
    print('Print Isabelle session names defined in DIRS.')
else:
    sessions = []
    for dir in sys.argv[1:]:
        sessions += get(dir)
    print('\n'.join(sessions))
