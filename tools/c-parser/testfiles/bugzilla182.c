/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
