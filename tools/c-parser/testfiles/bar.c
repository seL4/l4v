/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
