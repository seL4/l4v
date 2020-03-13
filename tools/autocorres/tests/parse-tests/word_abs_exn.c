/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Regression test: word_abstract on L2_catch/L2_call.
 */

int bad(int i) {
  return i == 0;
}

int bads(unsigned n) {
  unsigned i;
  for (i = 0; i < n; i++) {
    if (bad(i)) {
      return 1;
    }
  }
  return 0;
}
