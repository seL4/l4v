/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int y(int z);

int x(int a, int b)
{
    return y(a + b);
}

int y(int z)
{
    return x(z, z + 1) + x(z, z + 2);
}


int call_recursive(void)
{
    return y(3) + x(5, 9);
}

