/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned factorial(unsigned n)
{
    if (n == 0) {
        return 1;
    }
    return n * factorial(n - 1);
}

unsigned call_factorial(void)
{
    return factorial(42);
}
