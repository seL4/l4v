/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct x { int y; };

void
foo(void) {
    {
        int b;

        b = 1;
    }

    {
        struct x b = { 1 };
    }
}
