/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(int c)
{
  while (c < 10) {
    if (c < 0) { break; }
    c = c - 1;
  }
  return 3;
}

int g(int d)
{
  while (d < 10) {
    if (d < 0) { continue; }
    d = d - 1;
  }
  return 3;
}

int h(int e)
{
  while (e < 10)
    /** INV: "\<lbrace> True \<rbrace>" */
  {
    if (e < -10) { continue; }
    if (e < 0) { break; }
    e = e - 1;
  }
  return e;
}

int i(int x)
{
  int y;
  y = 10;
  while (x < 10) {
    while (x + y > 15) {
      if (x < 3) { break; }
      y = y - 2;
    }
    if (x < 3) { continue; }
  }
}

int dotest(int x)
{
  do {
    if (x < 10) break;
    x--;
  } while (x >= 10);
  return x;
}
