/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

typedef unsigned long uint32_t;

struct foo {
    uint32_t words[1];
};
typedef struct foo foo_t;

/** FNSPEC
  f_spec: "\<forall>i. \<Gamma> \<turnstile> \<lbrace> \<acute>i = i \<rbrace> \<acute>ret__unsigned :== PROC f(\<acute>i) \<lbrace> \<acute>ret__unsigned = i + 1 \<rbrace>"
*/
unsigned f(unsigned i)
{
  return (3 / i ? i+1 : i);
}


static inline void __attribute__((__pure__))
foo_ptr_new(foo_t *foo_ptr, uint32_t bar) {
  foo_ptr->words[0] = f(0);

  foo_ptr->words[0] |= bar << 0;
}

unsigned g(unsigned i)
{
  return f(i) + 3;
}

struct thing {
  int *base;
  int size;
};
typedef struct thing thing_t;

int h(thing_t t)
{
  for (int i = 0; i < t.size; i++) {
    t.base[i] = 0;
  }
  return t.size;
}


