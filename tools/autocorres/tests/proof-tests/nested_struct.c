/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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

void f(struct point1 *p1, struct point2 *p2)
{
    p1->x.n = p2->n[0];
    p2->n[1] = p1->y.n;
}

int test(struct point1 *p1, struct point2 *p2)
{
    f(p1, p2);
    return p1->x.n == p2->n[0] && p1->y.n == p2->n[1];
}

struct s1 {
    unsigned x, y;
};
struct s2 {
    struct s1 x[2];
};
struct s3 {
    struct s2 x, y;
};
struct s4 {
    struct s3 x[2];
};
void g(struct s4 *s)
{
    s->x[0].x.x[0].y = s->x[0].x.x[0].x;
    s->x[0].x.x[1] = s->x[0].x.x[0];
    s->x[0].y = s->x[0].x;
    s->x[1] = s->x[0];
    *s = *s;
}
