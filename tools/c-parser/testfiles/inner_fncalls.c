/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* this proto is for a function not defined in this translation unit */
int h(unsigned long);
int global;



int f(int x, int y)
{
  return global + h(6 * x) * y;
}

void e(int x)
{
  global = 3;
  global = f(x,2);
}

int g(int y)
{
  int local = global * (f(y - 2, y) + h(y));
  while (h(local)) {
    local += 10;
  }
  return f(local,h(7));
}


int f2(int x)
{
  return f(g(x + 1),g(6));
}

char function(int c) { return c + 1; }

int function2(int x) { return g(function(x)); }

