/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
