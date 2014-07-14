/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct list {
  int contents;
  struct list *next;
};

int last(struct list *nodeptr)
{
  if (!nodeptr) { return 0; }
  while (!nodeptr->next) {
    nodeptr = nodeptr->next;
  }
  return nodeptr->contents;
}
