/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int bad_names(void)
{
    int globals = 3;
    int myvars = 3;
    int P = 4;
    int A = 4;
    int B = 4;
    int R = 5;
    int L1_skip = 5;
    int L2_skip = 6;
    int L1_modify = 7;
    int L2_modify = 8;

    /* Following line used to kill local_var_extract. */
    int adglobs_addr = 4;

    return globals + P + R + A + B + myvars + L1_skip + L2_skip + L1_modify + L2_modify + adglobs_addr;
}

/* Also used to kill local_var_extract. */
int bad_vars(int symbol_table) {
  return symbol_table;
}

/* Testcase for VER-351. The C parser generates some StrictC'__assert_fail_foo param names
 * which we need to demangle carefully. */
void __assert_fail (const char *, const char *, int, const char *);
