/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned int plus(unsigned int a, unsigned int b) {
    return a + b;
}

unsigned int plus2(unsigned int a, unsigned int b) {
    while (b > 0) {
        a += 1;
        b -= 1;
    }
    return a;
}

int main(int argc, char **argv) {
    return !(plus(1, 2) == plus2(1, 2));
}
