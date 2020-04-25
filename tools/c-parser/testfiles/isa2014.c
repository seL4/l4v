/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x, y;

int f(int i)
{
  return i + 1;
}

int g(int *iptr)
{
  return iptr ? *iptr : 0;
}

/** MODIFIES: x */
void ff(int i)
{
  x += i * g(&y);
}
