/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int x)
{
  for (int i = 0; i < 10; i++ /** AUXUPD: foo */) {
    x = x + i;
  }
  return x;
}
