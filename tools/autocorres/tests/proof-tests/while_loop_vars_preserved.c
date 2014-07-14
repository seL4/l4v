/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned loop(unsigned dog, unsigned cat, unsigned mouse, unsigned horse)
{
    unsigned iterations = 0;
    while (dog > 0 || cat > 0 || mouse > 0 || horse > 0) {
        if (dog > horse) {
            dog--;
        } else if (horse > mouse) {
            horse--;
        } else if (cat > 0) {
            cat--;
        } else if (mouse > 0) {
            mouse--;
        } else if (dog > 0) {
            dog--;
        } else {
            horse--;
        }
        iterations++;
    }
    return iterations;
}

