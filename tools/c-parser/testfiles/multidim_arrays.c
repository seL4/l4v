/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int array[10][16];

struct s {
  int array[7][3];
};



int f(int i, int j)
{
  return array[i][j];
}

struct s global1, global2;

int g1(int *iptr)
{
  return iptr? *iptr : 0;
}

int g2(struct s* sptr, int i, int j)
{
  return sptr->array[i][j];
}

int h1(void)
{
  return g1(&global1.array[0][1]);
}

int h2(int i, int j)
{
  return g2(&global2, i, j);
}

