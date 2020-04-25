/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
