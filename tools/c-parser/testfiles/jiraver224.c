/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "includes/accentéd1.h"
#include "includes/accented大学.h"
#include "includes/accentedだいがく.h"

int g(int x)
{
  return included_f(x) + FOO + included_h(2);
}

struct s { char array[10]; } global_s;

char h(void)
{
  return included_j(global_s.array);
}
