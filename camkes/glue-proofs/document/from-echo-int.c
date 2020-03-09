/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int RPCFrom_echo_int(int i) {
    unsigned int _camkes_mr_index_12 = 0;

    /* Marshal the method index */
    seL4_SetMR(_camkes_mr_index_12, 0);
    _camkes_mr_index_12 += 1;

    /* Marshal all the parameters */
    seL4_SetMR(_camkes_mr_index_12, (seL4_Word) i);
    _camkes_mr_index_12 += 1;

    /* Call the endpoint */
    seL4_MessageInfo_t _camkes_info_13 =
        seL4_MessageInfo_new(0, 0, 0, _camkes_mr_index_12);
    (void)seL4_Call(6, _camkes_info_13);

    /* Unmarshal the response */
    _camkes_mr_index_12 = 0;
    int _camkes_ret_14 = (int)seL4_GetMR(_camkes_mr_index_12);
    _camkes_mr_index_12 += 1;

    return _camkes_ret_14;
}
