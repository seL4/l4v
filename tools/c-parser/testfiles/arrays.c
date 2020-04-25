/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int array[10];
char c_array[5];

typedef int i10[10];

int f(int i)
{
  return array[i];
}

i10 *f2(void)
{
  return &array;
}

int *g(int i)
{
  return &array[i];
}

void update(int i, int v)
{
  array[i] = v;
}

struct s {
  int a[10];
};

int h(struct s* sptr, int i)
{
  sptr->a[i-1] = i;
  return sptr->a[i];
}

int local(char c)
{
  char cs[6];
  for (int i = 0; i < 6; i++) cs[i] = c;
  return cs[0];
}

void ptr_parameter(int *ip, int i, int v)
{
  ip[i] = v;
}

void pass_array1(void)
{
  ptr_parameter(array, 3, 4);
}

void pass_array2(void)
{
  ptr_parameter(array + 4, 3, 4);
}

int array_deref(void)
{
  return *array;
}
