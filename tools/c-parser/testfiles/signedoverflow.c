/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(void)
{
  int j = 0;
  for (int i = 0; i < 10; i++)
    /** INV: "\<lbrace> 0 \<le> \<acute>i & \<acute>i \<le> 10 &
                        \<acute>j = 0 \<rbrace>" */
    {
      j = j * 2;
    }
  return j;
}


int g(int n)
{
  if ((unsigned)n == (1u << 31)) return -1;
  else return -n;
}
