/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

typedef struct {
  int x;
  char y;
} s_t;

s_t *s;

int f(void)
{
  int * const p = &(s->x);
  return *p;
}
