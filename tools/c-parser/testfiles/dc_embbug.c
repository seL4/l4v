/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* tests that when multiple embedded function calls to the same
   function occur within a function, that these do not cause a
   "multiple variables of the same name, danger, danger" error. */

int f(int n)
{
  return n + 1;
}

int h(int n)
{
  int m = n + f(3);
  {
    int x = n + f(6);
    if (x < 6) return x;
  }
  return n * f(n - 1);
}

