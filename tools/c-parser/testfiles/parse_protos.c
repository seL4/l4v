/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* this proto is for a function not defined in this translation unit */
int *h(unsigned long);

/* whereas this proto is used to enable mutual recursion (is a "forward"
   declaration). */
int g(int);

int f(int x)
{
  int *ptr;
  ptr = h(3);
  return g(*ptr + 1);
}

int g(int x)
{
  if (x == 0) { return 1; }
  else
    return f(x * 2);
}

int j(int foo);

int k(int x)
{
  return j(x + 1);
}
