/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
