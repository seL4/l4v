/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int fact(int n)
{
  unsigned factor, total;
  total = 1;
  factor = 2;
  while (factor <= n) {
    total = total * factor;
    factor = factor + 1;
  }
  return total;
}


