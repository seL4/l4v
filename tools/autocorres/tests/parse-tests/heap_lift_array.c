/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
