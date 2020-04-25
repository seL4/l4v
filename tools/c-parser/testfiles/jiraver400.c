/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int global;

int f(int i)
{
  int g(int);
  return g(i + 1);
}

int g(int j)
{
  if (j < 0) return 1;
  else return j * f(j - 1);
}

int h(void)
{
  return f(global * 2);
}

int indep1(int i)
{
  return i + 1;
}

int indep2(int i)
{
  int j = 1;
  for (; i < 10; i++) j++;
  return j;
}

int tree2a(int i)
{
  return i + 1;
}

int tree2b(int i)
{
  return i + 2;
}

int tree2c(int j)
{
  return tree2a(j) + tree2b(j * 3);
}
