/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

