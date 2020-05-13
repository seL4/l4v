/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned max(unsigned a, unsigned b)
{
    if (a <= b) {
        return b;
    }
    return a;
}

unsigned gcd(unsigned a, unsigned b)
{
    unsigned c;
    while (a != 0) {
        c = a;
        a = b % a;
        b = c;
    }
    return b;
}
