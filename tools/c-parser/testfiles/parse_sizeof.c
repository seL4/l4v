/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int j)
{
  return j + sizeof(j);
}

int g(void)
{
  int array[10] = {1,2,3,4,5};
  return array[sizeof(int)];
}

