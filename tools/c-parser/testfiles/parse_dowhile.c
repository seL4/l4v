/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

