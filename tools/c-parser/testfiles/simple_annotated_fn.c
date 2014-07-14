/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
