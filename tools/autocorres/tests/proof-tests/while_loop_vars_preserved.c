/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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

