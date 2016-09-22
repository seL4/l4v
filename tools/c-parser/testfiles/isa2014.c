/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int x, y;

int f(int i)
{
  return i + 1;
}

int g(int *iptr)
{
  return iptr ? *iptr : 0;
}

/** MODIFIES: x */
void ff(int i)
{
  x += i * g(&y);
}
