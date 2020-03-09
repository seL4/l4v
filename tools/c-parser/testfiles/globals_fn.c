/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x;

/* demonstrates updating and referencing a global variable */
int f(int n)
{
  x = x + 1;
  return x + n;
}

int garray[10];

void gupdate(int i, int value)
{
  garray[i] = value;
}

void update(int *array, int i, int value)
{
  array[i] = value;
}

int test1(void)
{
  update(garray, 3, 10);
  return garray[3];
}

int test2(void)
{
  return sizeof(garray);
}

int test3(int (*arrayptr)[10], int i)
{
  // this is wacky, but legitimate C
  return (*arrayptr)[i];
}

