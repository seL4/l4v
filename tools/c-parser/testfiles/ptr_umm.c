/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int swap(int *i, int *j)
{
  int tmp = *i;
  *i = *j;
  *j = tmp;
  return 0;
}
