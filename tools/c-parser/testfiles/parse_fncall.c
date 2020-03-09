/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int global;


int f (int x)
{
  return x + 2;
}

int h(int);

int g(int y)
{
  int z, u;
  z = f(y);
  u = h(3);
  return z + 3;
}

int h(int x)
{
  return x - 1;
}

int i(int x, int y)
{
  int z;
  z = h(x);
  return z + y;
}

void k(int x);
int j(int x)
{
  int z, u;
  k(3);
  z = f(x - 1);
  u = i(z, z + x);
  return z - u;
}

void k(int x)
{
  global = x;
}
