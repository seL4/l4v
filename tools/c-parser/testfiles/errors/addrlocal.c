/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

void swap(int *i1, int *i2)
{
  int tmp;
  tmp = *i1;
  *i1 = *i2;
  *i2 = tmp;
}

int f(void)
{
  int i = 1;
  int j = 2;

  swap(&i, &j);
  return j;
}
