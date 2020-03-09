/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int x)
{
  int i = 10;
  unsigned *ptr;
  while (i / x + 1) x--;
  for (*ptr = 3; i / *ptr > 4; ptr++);
  return x + 1;
}
