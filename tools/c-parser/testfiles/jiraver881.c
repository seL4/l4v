/*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

int f(void);

struct two_int {
    int first, second;
};

void baseline1(void) {
    int x;
    x = f();
}

int baseline2(void) {
    return f();
}

void test1(void) {
    unsigned y;
    y = f();
}

void test2(void) {
    struct two_int t;
    t.first = f();
}

void test3(void) {
    int z[2];
    z[0] = f();
}

unsigned test4(void) {
    return f();
}

struct two_int test5(void) {
    return (struct two_int) { .first = f() };
}
