/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* parsing test for local variable initialisation */

int f(int n)
{
  int m = n + 3, j = 1;
  unsigned i = 0;
  while (n < m) { m = m + 1; n = n + 2; }
  return m;
}
