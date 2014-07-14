/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int x /** OWNED_BY foo */, y /** OWNED_BY bar */, z;

/* reads/writes x, writes z */
int f(int i)
{
  x += i;
  z++;
  return x;
}

/* reads x & z, writes y */
int g(int i)
{
  y++;
  return x + i + z;
}
