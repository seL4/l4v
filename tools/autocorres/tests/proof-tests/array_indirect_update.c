/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Regression for VER-320 and other array-related bugs.
 */

int array[10];

void foo(int *a)
{
    *a = 3;
}

void bar(void)
{
    foo(&array[4]);
}
