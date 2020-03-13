/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int fact(unsigned int n)
{
  unsigned int total, factor;
  total = 1;
  factor = 2;
  while (factor <= n)
    /** INV: "\<lbrace>\<acute>factor * \<acute>total = FACT \<acute>factor  & \<acute>factor <= max 2 (\<acute>n + 1) \<rbrace>" */
    {
      total = total * factor;
      factor = factor + 1;
    }
  return total;
}
