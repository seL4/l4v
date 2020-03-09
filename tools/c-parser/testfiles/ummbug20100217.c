/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
