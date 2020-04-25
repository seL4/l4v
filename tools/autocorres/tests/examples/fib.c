/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned fib(unsigned n)
{
    if (n == 0) {
        return 0;
    }
    if (n == 1) {
        return 1;
    }
    return fib(n - 1) + fib(n - 2);
}

unsigned fib_linear(unsigned n)
{
    unsigned a = 0, b = 1;
    while (n) {
        unsigned t = b;
        b += a;
        a = t;
        n -= 1;
    }
    return a;
}

void call_fib(void)
{
    fib(42);
}
