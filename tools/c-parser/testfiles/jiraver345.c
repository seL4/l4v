/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
