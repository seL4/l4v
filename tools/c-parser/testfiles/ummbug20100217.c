/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct k {
  unsigned short b;
  char c[2];
};

/* two addressed globals */
struct k globkarray[10];
int globintarray[2];


int g(int n, struct k *kptr)
{
  return n + kptr->b;
}


int h(int *iptr)
{
  return g(*iptr, globkarray);
}

int j(void)
{
  return h(globintarray);
}
