/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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


