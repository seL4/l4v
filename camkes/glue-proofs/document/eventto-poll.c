/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int EventTo_poll(void) {
    seL4_Word *badge = get_badge();
    seL4_Poll(6, badge);
    return *badge == PENDING;
}
