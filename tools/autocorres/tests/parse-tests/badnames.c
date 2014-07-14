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

