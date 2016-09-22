/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
