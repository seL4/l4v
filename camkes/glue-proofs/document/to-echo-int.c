/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

static unsigned int echo_int_internal(void) {
    /* Unmarshal parameters */
    unsigned int _camkes_mr_27 = 1;
    int *i = get_echo_int_i();
    *i = seL4_GetMR(_camkes_mr_27);
    _camkes_mr_27 += 1;

    /* Call the implementation */
    int _camkes_ret_28 = RPCTo_echo_int(*i);

    /* Marshal the response */
    _camkes_mr_27 = 0;
    seL4_SetMR(_camkes_mr_27, _camkes_ret_28);
    _camkes_mr_27 += 1;

    return _camkes_mr_27;
}
