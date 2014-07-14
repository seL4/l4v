/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
