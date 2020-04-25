/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct s1 { int fld1; char c; };

typedef struct s1 stype;

int f(int n)
{
  stype foo;
  struct s2 {int myfld; char *cptr;};
  struct s2 bar;
  return bar.myfld + n + foo.c;
}
