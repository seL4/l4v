/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int n)
{
  int total = 1;
  do {
    total = total * n;
    n--;
  } while (n >= 0);
  return total;
}

int g(int x, int y)
{
  do
    /** INV: "\<lbrace> \<acute>x > \<acute>y \<rbrace>" */
    x += y;
  while (y < 100);
  return x;
}

int h(int x)
{
  do
    /** INV: "\<lbrace> \<acute>x > \<acute>y \<rbrace>" */
    {
      x ++;
    }
  while (x < 100);
  return x;
}

