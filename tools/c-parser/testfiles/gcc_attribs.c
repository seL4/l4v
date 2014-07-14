/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int array1[10][20] __attribute__((foo)) __attribute__((bar));

void f(int pos1, int pos2, int val)
{
  array1[pos1][pos2] = val;
}

__attribute__((noreturn))
int myexit(int);

int myexit2(int, int) __attribute__((noreturn));

