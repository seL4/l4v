/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int global;

int __attribute__((__const__)) baz(void) {
  return 3;
}

int __attribute__((const)) qux(void) {
  /* shouldn't fail with "syntax error: deleting  CONST" */
  return 4;
}
