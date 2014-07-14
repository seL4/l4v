/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int fact(int n)
{
  unsigned factor, total;
  total = 1;
  factor = 2;
  while (factor <= n) {
    total = total * factor;
    factor = factor + 1;
  }
  return total;
}


