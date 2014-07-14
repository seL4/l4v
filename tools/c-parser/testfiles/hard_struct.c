/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct s {
  int fld;
  struct t *ptr;
};

typedef struct s foo;

enum { MAX_T = 100 };

struct t {
  foo eek[MAX_T];
  int valid;
};

foo global;

foo mk_foo(int i)
{
  return (foo){.fld = i, .ptr = 0};
}


