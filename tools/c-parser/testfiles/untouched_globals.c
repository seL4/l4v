/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x, y = 1;

struct s { char c; int array[4]; };

struct s glob1, glob2 = { '3', 1,2 };

int f(int n)
{
  y++;
  return n + 1;
}

int g(int n)
{
  return n*n;
}
