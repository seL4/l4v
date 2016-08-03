/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*
 * Heap lifting for arrays.
 * Regression: JIRA VER-423.
 *
 * Unlike {read,write}_to_global_array.c, this takes the address of foo,
 * forcing C-parser to place it in symbol_table and not the globals record.
 * This tests the ability of AutoCorres to translate to the correct
 * heap access constructs on the lifted heap.
 */

unsigned int foo[10];

unsigned int bar(void) {
    foo[1] = 42;
    return foo[1];
}

unsigned int baz(void) {
    unsigned int *qux = foo;
    return qux[1];
}

unsigned int fuzz(unsigned int bizz[][10]) {
    return bizz[1][1];
}
