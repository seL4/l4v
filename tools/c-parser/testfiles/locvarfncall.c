/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int global;

int mult(int x, int y)
{
  return x * y;
}

int f(int x) { return x + 1; }
int g(int y) { return y * 2; }

int something(void)
{
  int r;
  r = mult(f(7), g(7));
  return r;
}

int something_else(int i)
{
  return mult(f(i),g(i+1));
}

int another(int i)
{
  int x = mult(f(i), g(i+1));
  return x + 1;
}

