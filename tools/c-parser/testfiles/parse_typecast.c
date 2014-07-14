/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned main(unsigned int j, int d)
{
  int *c = (int *)j;
  return (unsigned) (c + d);
}

void set_intptr(void *ptr, int val)
{
  *(int *)ptr = val;
}
