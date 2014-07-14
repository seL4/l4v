/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(int x, char c)
{
  while (x > 10) { x++; c *= 2; }
  int z = c;
  while (c < 100) {
    c += x;
    int w = c / 2;
    x -= w;
  }
  return c;
}
