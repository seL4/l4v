/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*
 * LocalVarExtract inserts a return statement after the inner conditional
 * block [1], because it's not obvious that the block never returns.
 * This causes PrettyBoundVarNames to barf when trying to find a return
 * variable name.
 *
 * Jira issue VER-591.
 */

int fact(int n) {
  int r = 1;
  for (;; n--) {
    if (n > 0) {
      r *= n;
    } else {
      if (n == 0) {
        break;
      } else {
        return 0;
      }
      /* [1] ... over here */
    }
  }
  return r;
}
