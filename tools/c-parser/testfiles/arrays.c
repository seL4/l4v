/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
