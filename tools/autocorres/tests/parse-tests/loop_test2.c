/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int moocow(void)
{
    int a;
    a = 3;
    while (a < 3)
        a++;
    if (a % 54 == 0) {
        a++;
    } else {
        a--;
    }
}


