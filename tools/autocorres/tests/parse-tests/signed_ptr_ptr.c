/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

static int *arr_ptr_1;
static int arr_1[120];

static int **foo(void)
{
    arr_ptr_1 = arr_1;
    return &arr_ptr_1;
}

