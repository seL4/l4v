/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/** MODIFIES: */
unsigned bodyless(void);

unsigned call_bodyless(void)
{
    return bodyless() + 1;
}

