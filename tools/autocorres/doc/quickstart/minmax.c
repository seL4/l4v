/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#define UINT_MAX (-1u)

/*
 * Simple pure functions.
 */

unsigned min(unsigned a, unsigned b) {
  if (a <= b) {
    return a;
  } else {
    return b;
  }
}

unsigned max(unsigned a, unsigned b) {
  return UINT_MAX - (
      min(UINT_MAX - a, UINT_MAX - b));
}

