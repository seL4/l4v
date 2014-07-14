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
  int i;
  char c;
  char *ptr;
};

struct s mk_s (int j)
{
  struct s result;
  result.i = j;
  result.c = 0;
  result.ptr = 0;
  return result;
}
