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
 * Simple test cases for heap_abs_syntax feature.
 * JIRA issue ID: VER-356
 */

struct thing {
  int x;
  int *p;
  struct thing *left;
  struct thing *right;
};

struct list {
  int x;
  struct list *p;
};

void f1(struct thing *t) {
  *t->p = 42;
}

void f2(struct thing *t) {
  t->x = 42;
}

void f3(struct thing *t) {
  t->right = t->left + 1;
}

void f4(struct thing *t) {
  t->left = t;
}

void f5(struct thing *p, struct thing t) {
  *p = t;
}

/* Signed word updates are still not translated correctly. */
void f6(long long *p) {
  *p = 42;
}

void f7(unsigned long long *p) {
  *p = 42;
}

int f8(struct list *l, struct thing *t) {
  return l->p->x && t->left->right->x;
}
