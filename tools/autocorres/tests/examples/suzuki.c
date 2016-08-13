/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct node {
  struct node *next;
  int data;
};
int suzuki(struct node *w, struct node *x, struct node *y, struct node *z) {
  w->next = x; x->next = y; y->next = z; x->next = z;
  w->data = 1; x->data = 2; y->data = 3; z->data = 4;
  return w->next->next->data; /* returns 4 */
}
