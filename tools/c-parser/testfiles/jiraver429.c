/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */



unsigned int foo(unsigned int *bar) {
  if (bar != 0) {
    return *bar;
  }
  return 0;
}
