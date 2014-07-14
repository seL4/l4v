/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int good(int *p) {
  return p && *p == 0;
}

struct ure {
  int n;
};

int bad(struct ure *sp) {
  return sp && sp->n == 0;
}
