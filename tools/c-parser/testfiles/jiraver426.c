/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

_Noreturn void exit(int i);

unsigned f(unsigned i)
{
  if (i < 0) exit(-1);
  return i * i;
}

_Noreturn void myexit(int i)
{
  exit(i + 1);
}
