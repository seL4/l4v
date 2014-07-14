/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

