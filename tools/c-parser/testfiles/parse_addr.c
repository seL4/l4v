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
char c;


int *f (int *array)
{
  return &array[10];
}

int a[10];
int a2[10];
int b1[10][10];
int b2[10][10];
int ca[10];
int d[10][10];

struct s {
  int arrayfld[10];
  int data;
};

struct s s1, s2;

int *f2(void)
{
  int y = *f(&b1[5][4]);
  int z = *f(b2[3]);
  int q = *f(s1.arrayfld);
  int q2 = *f((int *)a);
  return f(&a[6] + y + z + ca[5] + d[3][2] + q + s2.arrayfld[3] + *a2);
}

int *g(int c)
{
  return &x + c;
}

int h(void)
{
  return c + *f(&x);
}


