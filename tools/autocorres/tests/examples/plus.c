/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int plus(unsigned int a, unsigned int b)
{
    return a + b;
}

unsigned int plus2(unsigned int a, unsigned int b)
{
    while (b > 0) {
        a += 1;
        b -= 1;
    }
    return a;
}

int main(int argc, char **argv)
{
    return !(plus(1, 2) == plus2(1, 2));
}
