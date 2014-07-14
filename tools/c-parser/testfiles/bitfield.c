/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
