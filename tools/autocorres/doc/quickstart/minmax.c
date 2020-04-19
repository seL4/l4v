/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#define UINT_MAX (-1u)

/*
 * Simple pure functions.
 */

unsigned min(unsigned a, unsigned b)
{
    if (a <= b) {
        return a;
    } else {
        return b;
    }
}

unsigned max(unsigned a, unsigned b)
{
    return UINT_MAX - (
               min(UINT_MAX - a, UINT_MAX - b));
}

