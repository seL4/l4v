/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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


