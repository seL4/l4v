/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

void swap(int *i1, int *i2)
{
  int tmp;
  tmp = *i1;
  *i1 = *i2;
  *i2 = tmp;
}

int f(void)
{
  int i = 1;
  int j = 2;

  swap(&i, &j);
  return j;
}
