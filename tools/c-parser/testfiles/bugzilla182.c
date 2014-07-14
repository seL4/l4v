/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct small {
  int fld;
};

struct moderate {
  struct small many[10][10];
};

struct small array[10][10];

int f(int i, int j, struct moderate *mptr)
{
  return mptr->many[i][j].fld;
}

void g(int *ptr, int val)
{
  *ptr = val;
}

void h(int i, int j)
{
  g(&array[i][j].fld, 3);
}
