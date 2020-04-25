/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int nested_break_continue(int a, int b, int c)
{
    while (a < b) {
        while (b < c) {
            while (c < 4) {
                c++;
                if (c % 4 == 0)
                    break;
                if (c % 4 == 1)
                    return a;
                if (c % 4 == 2)
                    continue;
            }
            if (b % 4 == 0)
                break;
            if (b % 4 == 1)
                return b;
            if (b % 4 == 2)
                continue;
        }
        if (a % 4 == 0)
            break;
        if (a % 4 == 1)
            return a;
        if (a % 4 == 2)
            continue;
    }
    return 0;
}


