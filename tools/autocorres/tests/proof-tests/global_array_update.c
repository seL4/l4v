/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */


static int foo[1024];

void bar(void)
{
    /* Index 3 is thrown away. */
    foo[3] = 42;
}
int * bar2(void)
{
    return &foo[3];
}

