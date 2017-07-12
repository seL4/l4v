/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

