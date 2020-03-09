/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int f(void)
{
  return 0xffffffff;
}

char g(void)
{
  unsigned i = 0xffffffff;
  return i & 0xca;
}
