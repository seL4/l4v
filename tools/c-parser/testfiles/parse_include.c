/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#include "test_include2.h"
/* above defines included_fn, and included_global */

int g(int m)
{
  return m + included_global;
}

int h(char c)
{
  return included_fn(2 * c);
}

int included_fn(int param)
{
  return param * 3;
}
