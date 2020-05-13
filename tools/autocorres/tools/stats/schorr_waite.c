/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


#define NULL ((void *)0)

struct node {
    struct node *l, *r;
    unsigned m, c;
};

/* This is Mehta & Nipkow's version of the algorithm (HOL/Hoare/SchorrWaite.thy). */
void schorr_waite(struct node *root)
{
    struct node *t = root, *p = NULL, *q;
    while (p != NULL || (t != NULL && !t->m)) {
        if (t == NULL || t->m) {
            if (p->c) {
                q = t;
                t = p;
                p = p->r;
                t->r = q;
            } else {
                q = t;
                t = p->r;
                p->r = p->l;
                p->l = q;
                p->c = 1;
            }
        } else {
            q = p;
            p = t;
            t = t->l;
            p->l = q;
            p->m = 1;
            p->c = 0;
        }
    }
}

