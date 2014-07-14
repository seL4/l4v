/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

extern int x;

extern int array[];

int x;

int f(void)
{
  return x + 1;
}

int *g(void)
{
  return &x;
}

int array[40];

int index(int i)
{
  if (0 <= i && i < 40) return array[i];
  else return -1;
}

int update(int i, int value)
{
  array[i] = value;
}

enum { FOO = 30 };

extern int array2[];

int h(int i)
{
  return array2[i];
}

int array2[FOO / 2];





