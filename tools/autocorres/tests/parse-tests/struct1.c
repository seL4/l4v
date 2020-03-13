/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int g_1;
int k_1;
struct moo {
    int a;
    int b;
} cow;

int f_1(int x)
{
    return x;
}

int foo_1(void)
{
    return 3 ^ 3;
}

int bar_1(void)
{
    struct moo a;
    short x;

    foo_1();
    a.a = foo_1();
    cow.a = foo_1();
    g_1 = foo_1();
    k_1 += foo_1();
    x = (short)foo_1();
    f_1(f_1(foo_1()));

    return a.a;
}

