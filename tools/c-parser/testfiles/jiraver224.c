/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
