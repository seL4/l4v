/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int r(void)
{
    return r();
}

int fact(int n)
{
    if (n == 0)
        return 1;
    return n * fact(n - 1);
}

unsigned fact_unsigned(unsigned n)
{
    if (n == 0)
        return 1;
    return n * fact_unsigned(n - 1);
}

int call_recursive(void)
{
    return r() + fact_unsigned(3) + fact(3);
}

int call_recursive2(void)
{
    return call_recursive();
}

