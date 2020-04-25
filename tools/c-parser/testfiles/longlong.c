/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
