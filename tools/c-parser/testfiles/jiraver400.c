/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int global;

int f(int i)
{
  int g(int);
  return g(i + 1);
}

int g(int j)
{
  if (j < 0) return 1;
  else return j * f(j - 1);
}

int h(void)
{
  return f(global * 2);
}

int indep1(int i)
{
  return i + 1;
}

int indep2(int i)
{
  int j = 1;
  for (; i < 10; i++) j++;
  return j;
}

int tree2a(int i)
{
  return i + 1;
}

int tree2b(int i)
{
  return i + 2;
}

int tree2c(int j)
{
  return tree2a(j) + tree2b(j * 3);
}
