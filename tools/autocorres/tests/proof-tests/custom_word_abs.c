/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
