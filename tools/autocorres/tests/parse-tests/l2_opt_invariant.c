/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
