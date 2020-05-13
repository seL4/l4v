/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct node {
    int data;
    struct node *next;
};

struct node *insert(struct node *x, struct node *list)
{
    x->next = list;
    return x;
}

struct node *sorted_insert(struct node *x, struct node *list)
{
    struct node *prev = 0, *cur = list;
    while (cur) {
        if (cur->data >= x->data) {
            if (prev) {
                prev->next = x;
                x->next = cur;
                return list;
            } else {
                x->next = list;
                return x;
            }
            prev = cur;
            cur = cur->next;
        }
    }
    x->next = 0;
    prev->next = x;
    return list;
}

struct node *reverse(struct node *list)
{
    struct node *rev = 0;
    while (list) {
        struct node *next = list->next;
        list->next = rev;
        rev = list;
        list = next;
    }
    return rev;
}

struct node *revappend(struct node *list, struct node *dest)
{
    while (list) {
        struct node *next = list->next;
        list->next = dest;
        dest = list;
        list = next;
    }
    return dest;
}
