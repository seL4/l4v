/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int g(unsigned int x) { return x + 3; }

int f(int * x) { return *x + 1; }

int h(int x, int *y)
{
  return g(x) + f(y);
}

int j(int x)
{
  if (x > 4) {
    char c = x + 1;
    return c;
  } else {
    int c = x * 2;
    return c;
  }
}

unsigned long foo(unsigned int depth);

int bar(unsigned long baz)
{
    unsigned long depth;
    depth = bar(1);
}

struct b {
    struct b *x;
    int y;
};

int qux(int bbb)
{
    struct b *d, *baz;
    for(baz = (struct b *) 0; baz; baz = d)
    {
        d = baz->x;
    }
    return 1;
}

