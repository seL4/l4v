/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int array1[10];
int array2[10];
char array3[10];

struct s {
  int fld1;
  int array[1];
};

struct t {
  struct s v1, v2;
};

struct u {
  char carray[3];
  int iarray[3];
  struct s v;
};

int f(struct u uval)
{
  return uval.carray[0] + uval.iarray[1] + uval.v.fld1;
}
