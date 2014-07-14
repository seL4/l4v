/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
