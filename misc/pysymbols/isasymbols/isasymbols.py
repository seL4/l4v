#!/usr/bin/env python
# -*- coding: utf-8 -*-

#
# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

import codecs, collections, numbers, types

class IsaSymbolsException(Exception):
    pass

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

            fields = {'ascii_text':items[0]}

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

    def encode(self, data):
        for symbol in self.symbols:
            data = data.replace(symbol.ascii_text, unichr(symbol.code_point))
        return data

    def decode(self, data):
        for symbol in self.symbols:
            data = data.replace(unichr(symbol.code_point), symbol.ascii_text)
        return data

def make_translator(symbols_file):
    assert isinstance(symbols_file, basestring)
    with codecs.open(symbols_file, 'r', 'utf-8') as f:
        return Translator(f.read())
