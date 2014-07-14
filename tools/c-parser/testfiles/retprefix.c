/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned f(void)
{
  unsigned ret = 3;
  return ret;
}

int g(void)
{
  return 4;
}


int h(void)
{
  int ret = 2;
  int x = g();
  return x + ret;
}

int i(void)
{
  int ret = 2;
  return ret + g();
}
