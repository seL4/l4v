/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int *pdiff1 (int *ptr, int off)
{
  return ptr - off;
}

int pdiff2 (int *p1, int *p2)
{
  return p1 - p2;
}

struct testing_struct
{
  int val1;
  int val2;
};

int pdiff3 (struct testing_struct *p1)
{
  return ((int)(p1 + 1)) - ((int)(p1));
}
