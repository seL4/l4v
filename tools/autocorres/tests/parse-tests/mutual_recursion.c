/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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

