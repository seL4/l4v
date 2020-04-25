/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

void *memset(void *dest, int c, unsigned n)
{
    unsigned char *d = dest;
    while (n > 0) {
        *d = c;
        d++;
        n--;
    }
    return dest;
}

struct node {
    struct node *next;
    long data;
};

void zero_node(struct node *node)
{
    memset(node, 0, sizeof(struct node));
}

