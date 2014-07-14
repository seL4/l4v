/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

