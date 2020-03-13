/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int __attribute__ ((aligned (16))) u;
int v __attribute__ ((aligned (16)));

int f(int y)
{
  int __attribute__ ((aligned (16))) x = y * 2;
  return 3 + x;
}
