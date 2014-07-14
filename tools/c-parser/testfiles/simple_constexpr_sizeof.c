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
  char c;
  int x;
};

char f(struct s *sptr, int byteno)
{
  char array[sizeof(struct s)];
  for (int i = 0; i < sizeof *sptr; i++)
    array[i] = *(((char *)sptr) + i);
  return array[byteno];
}
