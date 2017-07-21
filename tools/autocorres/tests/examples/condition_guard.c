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

void f1(int *p) {
  if (p != NULL && *p == 0) *p = 1;
}

struct ure {
  int n;
};

void f2(struct ure *p) {
  if (p != NULL && p->n == 0) p->n = 1;
}

void fancy(int *p) {
  if (p != NULL && (p[0] == 0 || p[1] == 0)) {
    p[0] = p[1];
  }
}

void loop(int *p) {
  while (p != NULL && *p == 0) {
    p++;
  }
}

int arith(int x, int y) {
  return x / y == 0 || y / x == 0;
}
