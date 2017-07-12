/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* parsing test for local variable initialisation */

int f(int n)
{
  int m = n + 3, j = 1;
  unsigned i = 0;
  while (n < m) { m = m + 1; n = n + 2; }
  return m;
}
