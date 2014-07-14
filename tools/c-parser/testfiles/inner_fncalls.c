/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

