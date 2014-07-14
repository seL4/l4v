/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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

