/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x = 3, y = 4;

int array[] = {1,2,3,4,};
extern int a2[];

int *z = &y;
int u = sizeof(y);

enum { A = 3, B, C, D };

struct s {
  int data1;
  char data2;
} *sptr = (void *)0xdeadbeef;

typedef struct s s_t;

int a2[] = {B,A,C,D};

s_t sval = {.data2 = 3}, svalprime;

int f(int i)
{
  x += i + y + sptr->data1 + array[i] + *z;
  return x;
}

int g(void)
{
  return sval.data1 + svalprime.data2;
}


