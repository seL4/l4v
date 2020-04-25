/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int a(int x, int y)
{
    return x ^ ((x ^ y) & -(x < y));
}

unsigned b(unsigned x, unsigned y)
{
    return x & ((1U << y) - 1U);
}

unsigned c(unsigned x, unsigned y)
{
    return x > x + y;
}
