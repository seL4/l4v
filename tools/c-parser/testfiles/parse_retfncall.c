/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int add1(int n)
{
  return n + 1;
}

int add2(int n)
{
  return add1(n + 1);
}
