/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int x, char c)
{
  while (x > 10) { x++; c *= 2; }
  int z = c;
  while (c < 100) {
    c += x;
    int w = c / 2;
    x -= w;
  }
  return c;
}
