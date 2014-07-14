/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int x, y = 1;

struct s { char c; int array[4]; };

struct s glob1, glob2 = { '3', 1,2 };

int f(int n)
{
  y++;
  return n + 1;
}

int g(int n)
{
  return n*n;
}
