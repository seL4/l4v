/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(int x)
{
  int i = 10;
  unsigned *ptr;
  while (i / x + 1) x--;
  for (*ptr = 3; i / *ptr > 4; ptr++);
  return x + 1;
}
