#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import codecs
import collections
import numbers
import re
import types
from .exception import IsaSymbolsException


class Symbol(object):
    def __init__(self, ascii_text, code_point, group=None, font=None,
                 abbreviations=None):
        assert isinstance(ascii_text, basestring)
        assert isinstance(code_point, numbers.Number)
        assert isinstance(group, (basestring, types.NoneType))
        assert isinstance(font, (basestring, types.NoneType))
        assert isinstance(abbreviations, (collections.Iterable,
                                          types.NoneType))

        self.ascii_text = ascii_text
        self.code_point = code_point
        self.group = group
        self.font = font
        self.abbreviations = abbreviations or []


def _extract_property(prop):
    # Values of the symbol fields can contain '␣' which is intended to
    # indicate a space.
    return prop.replace(u'␣', ' ')


class Translator(object):
    def __init__(self, symbols_text):
        assert isinstance(symbols_text, basestring)

        self.symbols = []

        for number, line in enumerate(x.strip() for x in
                                      symbols_text.split('\n')):

            if line.startswith('#'):
                # Comment
                continue

            if line == '':
                # Blank line
                continue

            items = line.split()
            if len(items) < 3 or len(items) % 2 == 0:
                raise IsaSymbolsException('%d: unexpected line format' %
                                          number)

            fields = {'ascii_text': items[0]}

            for k, v in zip(*[iter(items[1:])] * 2):

                if k == 'code:':
                    try:
                        code = int(_extract_property(v), 16)
                    except ValueError:
                        raise IsaSymbolsException('%d: invalid code field' %
                                                  number)
                    fields['code_point'] = code

                elif k == 'group:':
                    fields['group'] = _extract_property(v)

                elif k == 'font:':
                    fields['font'] = _extract_property(v)

                elif k == 'abbrev:':
                    if 'abbreviations' not in fields:
                        fields['abbreviations'] = []
                    fields['abbreviations'].append(_extract_property(v))

                else:
                    raise IsaSymbolsException('%d: unexpected field %s' %
                                              (number, k))

            self.symbols.append(Symbol(**fields))

        # Translation dictionaries that we'll lazily initialise later.
        self._utf8_to_ascii = None
        self._utf8_to_tex = None
        self._hshifts_tex = None  # Handling for sub-/super-scripts

    def encode(self, data):
        for symbol in self.symbols:
            if symbol.ascii_text.startswith('\\<^'):
                continue
            data = data.replace(symbol.ascii_text, unichr(symbol.code_point))
        return data

    def decode(self, data):

        if self._utf8_to_ascii is None:
            # First time this function has been called; init the dictionary.
            self._utf8_to_ascii = {unichr(s.code_point): s.ascii_text
                                   for s in self.symbols}

        return ''.join(self._utf8_to_ascii.get(c, c) for c in data)

    def to_tex(self, data):
        '''
        Translate a string of Isabelle text into its TeX representation. This
        assumes the input is in unicode form. You probably do *not* want to use
        this functionality to go straight from THY files to TeX. The motivation
        for this is translating inline code in Markdown into something TeX-able.
        In particular, we assume all relevant Isabelle styles and preamble are
        already in scope.
        '''

        if self._utf8_to_tex is None:
            # First time this function has been called; init the dictionary.
            # XXX: Excuse this horror (don't worry; it used to be worse).
            self._utf8_to_tex = {
                unichr(s.code_point):
                    '{\\isasym%s}' % s.ascii_text[2:-1]
                for s in self.symbols
                if s.ascii_text.startswith('\\<') and
                    s.ascii_text.endswith('>')}

        if self._hshifts_tex is None:
            # XXX: Hardcoded
            self._hshifts_tex = (
                (re.compile(r'\\<\^sub>(.)'), r'\\textsubscript{\1}'),
                (re.compile(r'\\<\^sup>(.)'), r'\\textsuperscript{\1}'),
                (re.compile(r'\\<\^bold>(.)'), r'\\textbf{\1}'),
                (re.compile(r'\\<\^bsub>'), r'\\textsubscript{'),
                (re.compile(r'\\<\^bsup>'), r'\\textsuperscript{'),
                (re.compile(r'\\<\^esu\(b|p\)>'), '}'),
            )

        return ''.join(self._utf8_to_tex.get(c, c) for c in
                       reduce(lambda a, (regex, rep): regex.sub(rep, a), self._hshifts_tex,
                              data))


def make_translator(symbols_file):
    assert isinstance(symbols_file, basestring)
    with codecs.open(symbols_file, 'r', 'utf-8') as f:
        return Translator(f.read())
