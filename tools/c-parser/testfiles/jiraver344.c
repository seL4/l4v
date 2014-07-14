/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct __s {
  int fld;
  int __fld;
};

typedef struct __s __t;

int _f(int i)
{
  return i + 1;
}

int g(struct __s *sptr, __t *__x)
{
  return sptr->__fld + __x->__fld;
}
