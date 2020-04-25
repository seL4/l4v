/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Used to break l2_opt.
 * Because monad_equiv_unreachable' didn't instantiate the postcond
 * and left another subgoal with a schematic precond, which caused
 * something or other to break. It's a long story.
 *
 * JIRA issue VER-510
 */

void foo(int *x) {
  int z;
  if (!(*x)) {
    /* always fails */
    z = 1 / *x;
  }
}
