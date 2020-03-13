/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* test file for determining the a program's "state" */

typedef int * intptr;

struct s { int x, y; intptr p; };

extern int f(struct s *ptr, intptr p);

struct s svalue, *sptr;

int g(int x)
{
  unsigned int n;
  struct s svalue2, *sptr2;
  return (x + n);
}

struct s h(int y)
{
  struct s returnvalue;
  returnvalue.x = y;
  returnvalue.y = y;
  returnvalue.p = null;
  return (returnvalue);
}
