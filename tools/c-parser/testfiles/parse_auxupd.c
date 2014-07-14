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
  for (int i = 0; i < 10; i++ /** AUXUPD: foo */) {
    x = x + i;
  }
  return x;
}
