/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(int x, int y)
{
  switch (x) {
  case 0:
    x += y;
    break;
  case 1: case 2:
    x -= y * 2;
    return y;
  default:
    x -= y;
  }
  return x;
}


enum {foo = 101,bar};

int g(int y)
{
  int x;
  switch (y) {
  case foo:
    return f(y + 1, 0);
  case bar:
    x = y + 2;
    break;
  default:
    x = 4;
  }
  return x * 2;
}

int h(int z)
{
  switch (z) {
  case foo: case 2: default:
    return 3;
  case bar:
    return 4;
  }
}

int j(int z)
{
  switch (z) {
  case 1: return 3;
  case 2: return 4;
  }
  return 5;
}

int k(int z, int *array)
{
  switch (array[z]) {
  case 0: return 3;
  case 1: return 4;
  default: return 5;
  }
}
