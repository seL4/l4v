/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

void f(int i)
{
  int j;
  if (i && 10/i > 2) j = i + 1;
}

int deref(int *p)
{
  return *p;
}

int test_deref(int *p)
{
  if (p && deref(p) > 3) return 4;
  else return 0;
}

int imm_deref(int *p)
{
  if (p && *p > 4) return 4;
  else return 0;
}

int simple(int i)
{
  return (i > 4) && (i < 10);
}

struct foo {
  int data;
};

int condexp(int i, char *ptr, struct foo *ptr2)
{
  int j = i > 0 ? i - 1 : 3;
  char *p = 0 < j && simple(j) ? ptr : 0;
  int k = p ? *p : 10;
  struct foo p2prime = ptr2 ? *ptr2 : (struct foo){.data = 4};
  return j + k + p2prime.data;
}
