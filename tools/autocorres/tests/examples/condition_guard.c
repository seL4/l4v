/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * AutoCorres simplification of compound expressions.
 *
 * In C, each of the boolean expressions below is simple.
 * However, C-parser needs to generate a guard for some subexpressions,
 * and so it turns each expression into a complicated statement.
 *
 * One way to simplify them is by rewriting each expression into the form
 *   guard G; <use expr>
 * where G contains all the necessary guards for the expr.
 *
 * This makes it easier, for example, for the user to separate
 * the correctness and definedness qualities of the generated code.
 *
 * Currently, AutoCorres can do this simplification in some cases,
 * but cannot simplify any of the expressions below.
 */
#define NULL ((void*)0)

void f1(int *p)
{
    if (p != NULL && *p == 0) {
        *p = 1;
    }
}

struct ure {
    int n;
};

void f2(struct ure *p)
{
    if (p != NULL && p->n == 0) {
        p->n = 1;
    }
}

void fancy(int *p)
{
    if (p != NULL && (p[0] == 0 || p[1] == 0)) {
        p[0] = p[1];
    }
}

void loop(int *p)
{
    while (p != NULL && *p == 0) {
        p++;
    }
}

int arith(int x, int y)
{
    return x / y == 0 || y / x == 0;
}
