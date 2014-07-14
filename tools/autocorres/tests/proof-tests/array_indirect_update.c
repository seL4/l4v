/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
