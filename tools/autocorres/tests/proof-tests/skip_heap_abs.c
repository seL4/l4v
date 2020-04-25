/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Simple test for skip_heap_abs.
 */

int f(int *p)
{
    int n = *p;
    *p = n + 1;
    return n;
}
