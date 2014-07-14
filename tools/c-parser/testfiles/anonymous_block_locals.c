/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct x { int y; };

void
foo(void) {
    {
        int b;

        b = 1;
    }

    {
        struct x b = { 1 };
    }
}
