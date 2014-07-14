/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
