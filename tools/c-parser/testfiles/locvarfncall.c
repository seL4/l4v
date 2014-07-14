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

