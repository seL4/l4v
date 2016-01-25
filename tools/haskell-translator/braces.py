#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#


class BracedString:
    def __init__(self, s, l, r, bits=None):
        if bits == None:
            bits = self._get_bits(s, l, r)
        self.bits = bits
        self.s = s
        self.l = l
        self.r = r

    def _get_bits(self, s, l, r):
        i = 0
        bits = ['']
        for c in s:
            if c == l:
                if i == 0:
                    if bits[-1]:
                        bits.append('')
                i = i + 1
            bits[-1] = bits[-1] + c
            if c == r:
                i = i - 1
                if i == 0:
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
            s = ''
            internals = []
            for bit in self.bits:
                if bit.startswith(self.l):
                    s = s + self.l + self.r
                    internals.append(bit)
                else:
                    s = s + bit
            bits1 = s.split(str, num)
            bits = []
            bbs = []
            for bit in bits1:
                bits2 = bit.split(self.l + self.r)
                meshed = [bits2.pop(0)]
                while bits2:
                    meshed.append(internals.pop(0))
                    meshed.append(bits2.pop(0))
                meshed = [s for s in meshed if s != '']
                bbs.append(meshed)
                bits.append(''.join(meshed))
        return [BracedString(bit, self.l, self.r, bbs[i])
                for i, bit in enumerate(bits)]

    def startswith(self, s):
        return self.s.startswith('%s' % s)

    def endswith(self, s):
        return self.s.endswith('%s' % s)

    def map(self, fn):
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
    print x.split('=>')
    print x.split(',')
    print 1, x.split('=>', 1)
    print 2, x.split('=>', 2)
    print 3, x.split('=>', 3)
    print[y.split() for y in x.split('=>')]
