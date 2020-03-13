/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned lifted_a(unsigned *x)
{
    return *x;
}

unsigned unlifted_a(unsigned *x)
{
    return *x;
}

unsigned lifted_b(unsigned *x)
{
    return unlifted_a(x) + lifted_a(x) + *x;
}

unsigned unlifted_b(unsigned *x)
{
    return unlifted_a(x) + lifted_a(x) + *x;
}

