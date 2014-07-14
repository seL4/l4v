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
  int y;
  switch (x + 1) {
  case 0:
    y = x;
  case 1: case 2:
    y = 3;
    break;
  default:
    y = 4;
  }
  return y;
}

int g(int x)
{
  switch (x + 3) { };
  return 4;
}
