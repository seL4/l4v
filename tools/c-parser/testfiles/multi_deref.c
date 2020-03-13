/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


struct node {
    struct node *next;
    int v;
};

int f(struct node *n)
{
    return n->next->next->next->v;
}

unsigned g (unsigned **ptr)
{
  return **ptr;
}
