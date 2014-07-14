/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

