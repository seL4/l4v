/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Returns 1 iff the the element "v" is present in the sorted array "x" of
 * length "n".
 */
unsigned binary_search(unsigned *x, unsigned n, unsigned v)
{
    unsigned l = 0;
    unsigned r = n;
    unsigned found = 0;

    while (l < r && !found) {
        unsigned m = (l + r) / 2;
        unsigned d = x[m];
        if (d == v) {
            found = 1;
        } else if (d < v) {
            l = m + 1;
        } else {
            r = m;
        }
    }
    return found;
}

