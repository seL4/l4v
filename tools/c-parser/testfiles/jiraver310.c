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
  struct s *next;
  int data;
};

int * globalptr;

struct s f(int i)
{
  struct s node = {.data = i};
  return node;
}

struct s g(int i)
{
  globalptr = 0;
  return (struct s){.data = i, .next = 0};
}

struct s h(void)
{
  struct s node = {0};
  return node;
}
