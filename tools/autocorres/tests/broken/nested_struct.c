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
 * Accessing nested structs.
 * Testcase for bug VER-321.
 */
struct num {
  int n;
};

struct point1 {
  struct num x, y;
};

struct point2 {
  int n[2];
};

void f(struct point1 *p1, struct point2 *p2) {
  p1->x.n = p2->n[0];
  p2->n[1] = p1->y.n;
}

int test(struct point1 *p1, struct point2 *p2) {
  f(p1, p2);
  return p1->x.n == p2->n[0] && p1->y.n == p2->n[1];
}
