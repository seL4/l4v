/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x;

int *ptr;

int array[10];

int *f(int **p)
{
  int *ptrarray[10];
  return *p;
}
