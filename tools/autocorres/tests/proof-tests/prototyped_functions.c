/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */


unsigned int moo1(void);

void moo2(void);

void moo3(unsigned int x);

void moo4(void);

unsigned int cow(void)
{
    moo2();
    moo4();
    moo3(moo1());
    return moo1();
}

