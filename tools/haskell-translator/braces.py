#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

from __future__ import print_function


class BracedString:
    """A string split into components based on delimiters (usually braces).

    When l occurs in the string, create a new component whose contents are
    the rest of the string until the matching r.

    When l = ( and r = ), this has the approximate behavior of splitting
    the string into the components of a Haskell function application,
    where each individual component, if not containing the delimiters, can
    be split on white space to determine the arguments of the function.

    This behaves exactly like a str, except for split, map, and
    discard_enclosing_braces.

    Invariant: a component either has no delimiters, or is surrounded by
    delimiters.
    """

    def __init__(self, s, l, r, bits=None):
        if bits is None:
            bits = self._get_bits(s, l, r)
        self.bits = bits
        self.s = s
        self.l = l
        self.r = r

    def _get_bits(self, s, l, r):
        nesting_depth = 0
        bits = ['']
        for c in s:
            if c == l:
                if nesting_depth == 0:
                    if bits[-1]:
                        bits.append('')
                nesting_depth = nesting_depth + 1
            bits[-1] = bits[-1] + c
            if c == r:
                nesting_depth = nesting_depth - 1
                if nesting_depth == 0:
                    if bits[-1]:
                        bits.append('')
        if not bits[-1]:
            bits.pop(-1)
        return bits

    def __str__(self):
        return self.s

    def __repr__(self):
        check = BracedString(self.s, self.l, self.r)
        if check.bits == self.bits:
            return 'B%s%s: %r' % (self.l, self.r, self.s)
        else:
            return 'Broken Braced: %r, %r, %r' % (self.s, self.bits,
                                                  check.bits)

    def __add__(self, other):
        if isinstance(other, BracedString):
            if self.bits[-1].startswith(self.l):
                bits = self.bits + other.bits
            elif other.bits[0].startswith(self.l):
                bits = self.bits + other.bits
            else:
                bits = self.bits[:-1] + \
                    [self.bits[-1] + other.bits[0]] + \
                    other.bits[1:]
            return BracedString(self.s + other.s, self.l, self.r, bits)

        return BracedString(self.s + other, self.l, self.r)

    def __eq__(self, other):
        return other == self.s

    def __ne__(self, other):
        return other != self.s

    def __iter__(self):
        return iter(self.s)

    def __getitem__(self, n):
        return self.s[n]

    def __getslice__(self, i, j):
        return self.s.__getslice__(i, j)

    def __len__(self):
        return len(self.s)

    def split(self, str=None, num=-2, braces=False):
        """Split into multiple BracedStrings, using `str` as a delimiter, and
        into a maximum of `num` components.

        If `braces` is true (defaults to false), braces will also count as a
        delimiter, and each braced component will become a single element of
        the output.

        Otherwise, each braced pair will not be split into a separate
        component, but splitting will ignore the contents inside the
        delimiter.
        """
        if braces:
            bits = []
            bbs = []
            for bit in self.bits:
                d = num + 1 - len(bits)
                if d == 0:
                    bits[-1] = bits[-1] + bit
                    bbs[-1].append(bit)
                elif bit.startswith(self.l):
                    bits.append(bit)
                    bbs.append([bit])
                else:
                    if num == -2:
                        n_bits = bit.split(str)
                    else:
                        n_bits = bit.split(str, d)
                    bits.extend(n_bits)
                    bbs.extend([[b] for b in n_bits])
        else:
            # s is the original string, but with delimited substrings replaced
            # with just the delimiters
            s = ''
            internals = []
            for bit in self.bits:
                if bit.startswith(self.l):
                    s = s + self.l + self.r
                    internals.append(bit)
                else:
                    s = s + bit
            # split on the thing, secure in the knowledge that it won't mess
            # up things inside delimiters.
            bits1 = s.split(str, num)
            bits = []
            bbs = []
            for bit in bits1:
                # Invariant: if self.{l,r} not in bit, bit remains whole.

                # split on delimiters, which we inserted earlier
                bits2 = bit.split(self.l + self.r)
                meshed = [bits2.pop(0)]
                while bits2:
                    # If this list has more elements, then we need to insert,
                    # where each delimiter pair was, the corresponding
                    # contents which we stored in `internals`.
                    meshed.append(internals.pop(0))
                    # then we add in the next component of the string, which
                    # was after that delimiter pair.
                    meshed.append(bits2.pop(0))
                # remove empty strings
                meshed = [s for s in meshed if s != '']
                bbs.append(meshed)
                bits.append(''.join(meshed))

        return [BracedString(bit, self.l, self.r, bbs[i])
                for i, bit in enumerate(bits)]

    def startswith(self, s):
        return self.s.startswith(s)

    def endswith(self, s):
        return self.s.endswith(s)

    def map(self, fn):
        """Apply a function to each component of this braced string.

        For delimited components, the delimiters will not be passed to the
        function.
        """
        new_s = ''
        new_bits = []

        for bit in self.bits:
            if bit.startswith(self.l):
                new = fn(bit[1:-1])
                new = self.l + new + self.r
                new_s = new_s + new
                new_bits.append(new)
            else:
                new_s = new_s + bit
                new_bits.append(bit)

        return BracedString(new_s, self.l, self.r, new_bits)

    def discard_enclosing_braces(self):
        """If the string consists of one braced expression,
                discard the redundant enclosing braces. Otherwise
                return the string."""
        if len(self.bits) > 1:
            return self

        [bit] = self.bits

        if bit.startswith(self.l):
            return BracedString(bit[1:-1], self.l, self.r)
        else:
            return self


def clone(str, obj):
    if isinstance(obj, BracedString):
        return BracedString(str.__str__(), obj.l, obj.r)
    else:
        return str


str = BracedString

if __name__ == '__main__':
    x = BracedString('a => b => c => (d => (e, f))', '(', ')')
    print(x.split('=>'))
    print(x.split(','))
    print(1, x.split('=>', 1))
    print(2, x.split('=>', 2))
    print(3, x.split('=>', 3))
    print([y.split() for y in x.split('=>')])
