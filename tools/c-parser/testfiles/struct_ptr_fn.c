/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
