/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int array1[10][20] __attribute__((foo)) __attribute__((bar));

void f(int pos1, int pos2, int val)
{
  array1[pos1][pos2] = val;
}

__attribute__((noreturn))
int myexit(int);

int myexit2(int, int) __attribute__((noreturn));

