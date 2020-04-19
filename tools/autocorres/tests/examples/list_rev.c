/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#define NULL ((void *)0)

struct node {
    struct node *next;
    int data;
};

struct node *reverse(struct node *list)
{
    struct node *rev = NULL;
    while (list) {
        struct node *next = list->next;
        list->next = rev;
        rev = list;
        list = next;
    }
    return rev;
}

