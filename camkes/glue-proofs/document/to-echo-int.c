/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
