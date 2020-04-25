/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct node {
    struct node *next;
    int data;
};
int suzuki(struct node *w, struct node *x, struct node *y, struct node *z)
{
    w->next = x;
    x->next = y;
    y->next = z;
    x->next = z;
    w->data = 1;
    x->data = 2;
    y->data = 3;
    z->data = 4;
    return w->next->next->data; /* returns 4 */
}
