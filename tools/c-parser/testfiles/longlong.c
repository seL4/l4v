/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(long long x)
{
  return x % (1 << 31);
}

int g(long long x)
{
  return (x == 0);
}

int callg(void)
{
  long long n = ~0u;
  return g(n + 1);
}

long long shifts1(long long x, int i)
{
  return ((x << i) + (x >> i));
}

int shifts2(long long x, int i)
{
  return ((x << i) + (x >> i));
}

int literals(void)
{
  int x = 30LL;
  return x + 1;
}
