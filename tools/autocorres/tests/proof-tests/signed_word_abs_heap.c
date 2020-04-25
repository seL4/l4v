/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */
int foo(int *p, int e)
{
    int a = *p;
    if (e == 0) {
        return 0;
    } else {
        return e + a;
    }
}

int bar(int *p, int e)
{
    *p += e;
    return *p;
}
