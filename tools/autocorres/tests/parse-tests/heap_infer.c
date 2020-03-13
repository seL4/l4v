/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
Regression test: HeapLiftBase didn't look at recursive function definitions properly,
                 so it failed to infer that we needed a word32 heap here.
*/

unsigned foo(void) {
  return *(unsigned*)foo();
}
