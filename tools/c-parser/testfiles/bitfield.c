/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* parsing test for struct bitfields */

struct foo {
  int x:3;
  unsigned int y:5;
};

int g(struct foo *p)
{
  if (p) { return p->x + p->y; }
  return 0;
}
