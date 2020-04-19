/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct s {
    unsigned long x;
};

struct s f(struct s v)
{
    return v;
}
