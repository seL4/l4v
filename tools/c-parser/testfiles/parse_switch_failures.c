/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int x)
{
  int y;
  switch (x + 1) {
  case 0:
    y = x;
  case 1: case 2:
    y = 3;
    break;
  default:
    y = 4;
  }
  return y;
}

int g(int x)
{
  switch (x + 3) { };
  return 4;
}
