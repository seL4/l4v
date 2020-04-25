/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int main(unsigned int x)
{
    switch (x) {
        case 2:
            return 4;
        case 3:
            return 5;
        default:
            return -3;
    }
}

