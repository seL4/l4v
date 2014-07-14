/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
