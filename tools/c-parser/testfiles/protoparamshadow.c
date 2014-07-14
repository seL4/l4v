/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int var;

int proto(int var);

int realone(int var)
{
  return var + 1;
}

int f(void)
{
  var = var + 1;
  return var;
}

int var = 4;

