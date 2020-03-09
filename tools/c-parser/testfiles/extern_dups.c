/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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





