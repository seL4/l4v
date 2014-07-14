/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
