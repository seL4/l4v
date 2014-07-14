/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(int x, int y, unsigned u, unsigned v)
{
  return (x < y) + (x <= y) + (x >= y) + (x != y) + (u < v);
}

int g(int x, int y)
{
  return (x % y) * (x + y) / (x - y);
}

int condexp(int x, int y)
{
  return x ? y : y + 1;
}

int cbools(int i, int *p)
{
  int j = 10;
  while (j) { i++; j--; }
  return (i || !p) ;
}

int bitwise(int x, int y)
{
  return (x & y) + (x | y) + (x ^ ~y);
}

int shifts(int x, int y)
{
  return (x << y) + (x >> y);
}

char inc(int x)
{
  return x + 1;
}

int callbool(int y)
{
  y = condexp(inc(y) || inc(inc(y*2)), 3);
  return condexp(y > 3, y == 4 || y == 10);
}

int ptr_compare(void *vptr, int *x)
{
  return (x != vptr);
}

int large_literal_rshift (int w)
{
  return 0xF0000000 >> w;
}

void assignops(int *x, int y)
{
  *x >>= y;
  *x <<= y;
  *x += y;
  *x *= y;
  *x /= y;
  *x ^= y;
  *x -= y;
  *x &= y;
  *x |= y;
  *x %= y;
  *x = y;
}
