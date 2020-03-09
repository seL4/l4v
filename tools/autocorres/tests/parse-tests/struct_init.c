/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct bar {
    int a;
};

struct foo {
    struct bar *x;
};

int main(void)
{
    struct foo y = {0};
    return 0;
}
