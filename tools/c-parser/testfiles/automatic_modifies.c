/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x, y;

int array1[10], array2[20];

int *ptr;

int f(void)
{
  x = 3;
  return y;
}

void g1(int i)
{
  array1[i] = f();
}

void g2(int j)
{
  *ptr = f();
}

void h(int i)
{
  g1(i);
}

void ifn(int *p, int i)
{
  *p = i;
}

void jfn(void)
{
  ifn(array2 + 3);
}

void k(void)
{
  y = f();
}

void mrec2(void);
void mrec1(void)
{
  int tmp = mrec2();
  array1[f()] = tmp;
}

void mrec2(void)
{
  if (x > 4) mrec1();
  else y = 10;
}

int a(void)
{
  mrec2();
  return 3;
}
