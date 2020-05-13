/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


static int foo[1024];

void bar(void)
{
    /* Index 3 is thrown away. */
    foo[3] = 42;
}
int *bar2(void)
{
    return &foo[3];
}

