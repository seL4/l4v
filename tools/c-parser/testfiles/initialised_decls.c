/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned y;

unsigned f(unsigned x)
{
  y++;
  return x + 1;
}


int g(void)
{
  unsigned i = f(6);
  return 3;
}
