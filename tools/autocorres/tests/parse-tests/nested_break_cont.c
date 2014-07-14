/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int nested_break_continue(int a, int b, int c)
{
    while (a < b) {
        while (b < c) {
            while (c < 4) {
                c++;
                if (c % 4 == 0)
                    break;
                if (c % 4 == 1)
                    return a;
                if (c % 4 == 2)
                    continue;
            }
            if (b % 4 == 0)
                break;
            if (b % 4 == 1)
                return b;
            if (b % 4 == 2)
                continue;
        }
        if (a % 4 == 0)
            break;
        if (a % 4 == 1)
            return a;
        if (a % 4 == 2)
            continue;
    }
    return 0;
}


