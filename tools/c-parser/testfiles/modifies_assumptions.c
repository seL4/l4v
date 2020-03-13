/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x, y, z;
int a[10], b[6];

/** MODIFIES: x a b */
int f(void);

int g(int i)
{
  z = f();
  return i + z;
}

void h(int *a, int i)
{
  *a = i;
}

void j(void)
{
  h(a,z);
}

void k(int i, int v)
{
  b[i] = v;
}
