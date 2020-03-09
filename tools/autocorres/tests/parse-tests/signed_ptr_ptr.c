/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

static int *arr_ptr_1;
static int arr_1[120];

static int **foo(void)
{
    arr_ptr_1 = arr_1;
    return &arr_ptr_1;
}

