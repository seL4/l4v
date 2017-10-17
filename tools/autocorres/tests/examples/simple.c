/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned max(unsigned a, unsigned b) {
    if (a <= b)
        return b;
    return a;
}

unsigned gcd(unsigned a, unsigned b) {
    unsigned c;
    while (a != 0) {
        c = a;
        a = b % a;
        b = c;
    }
    return b;
}
