/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Initialiser for void*; fixed in git-aa162a0.
 */

struct A {
  void *p;
};

void f(void) {
  struct A a = { 0 };
}
