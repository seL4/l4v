/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * LocalVarExtract inserts a return statement after the inner conditional
 * block [1], because it's not obvious that the block never returns.
 * This causes PrettyBoundVarNames to barf when trying to find a return
 * variable name.
 *
 * Jira issue VER-591.
 */

int fact(int n)
{
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
