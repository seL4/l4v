/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

void f (int *ptr)
{
  *ptr = *ptr + 1;
  return;
}

void g (int *ptr)
{
  *ptr += 1;
}
