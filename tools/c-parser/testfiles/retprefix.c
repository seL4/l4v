/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned f(void)
{
  unsigned ret = 3;
  return ret;
}

int g(void)
{
  return 4;
}


int h(void)
{
  int ret = 2;
  int x = g();
  return x + ret;
}

int i(void)
{
  int ret = 2;
  return ret + g();
}
