/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

void* memset(void *dest, int c, unsigned n)
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

