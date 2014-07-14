/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int f(int j)
{
  return j + sizeof(j);
}

int g(void)
{
  int array[10] = {1,2,3,4,5};
  return array[sizeof(int)];
}

