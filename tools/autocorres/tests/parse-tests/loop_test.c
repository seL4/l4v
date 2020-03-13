/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned int uint;

uint moop;

uint f(uint a, uint b, uint c)
{
    return a + b + c;
}

uint foo(uint xy, uint z)
{
    uint *xx = &moop;
    uint t = 3;
    uint y = 1;
    uint q = 3;
    *xx = 3;
    uint i;
    uint n = 3;

    while (t < 10 && t < n) {
        t += y;
        y += q;
        if (t > 10)
            break;
        else
            continue;
    }


    while (i < n  && i < 42) {
        f(i,i+1,i+2);
        i++;
    }

    return t + y + q;
}


