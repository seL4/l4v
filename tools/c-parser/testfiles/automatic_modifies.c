/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
