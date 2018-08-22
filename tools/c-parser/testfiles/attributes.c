/*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

int __attribute__ ((aligned (16))) u;
int v __attribute__ ((aligned (16)));

int f(int y)
{
  int __attribute__ ((aligned (16))) x = y * 2;
  return 3 + x;
}
