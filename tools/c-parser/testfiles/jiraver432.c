/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct {
  int fld1;
  char fld2;
  _Bool fld3;
} global1;

struct {
  int fld;
} global2;

char f(void)
{
  global1.fld1++;
  return global1.fld2;
}
