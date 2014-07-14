/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
