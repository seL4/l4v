/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#define NULL ((void *)0)

struct node {
  struct node *next;
  int data;
};

struct node *reverse(struct node *list) {
    struct node *rev = NULL;
    while (list) {
        struct node *next = list->next;
        list->next = rev; rev = list; list = next;
    }
    return rev;
}

