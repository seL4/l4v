/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int global;

int __attribute__((__const__)) baz(void) {
  return 3;
}

int __attribute__((const)) qux(void) {
  /* shouldn't fail with "syntax error: deleting  CONST" */
  return 4;
}
