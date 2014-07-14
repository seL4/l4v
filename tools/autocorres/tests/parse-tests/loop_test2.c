/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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


