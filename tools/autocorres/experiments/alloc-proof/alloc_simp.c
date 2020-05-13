/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// #define VERIFIED 1

#ifndef VERIFIED
#include <stdlib.h>
#include <stdio.h>
#endif

#ifndef NULL
#define NULL ((void *)0)
#endif

typedef unsigned long word_t;

struct heap {
    word_t max;
    word_t curr;
};

void init_heap(struct heap *heap, word_t max)
{
    heap->curr = (word_t) malloc(max);
    //printf("%lu\n", heap->curr);
    heap->max  = heap->curr + max;
}

void *alloc(struct heap *heap, word_t bytes)
{
    if (heap->curr + bytes > heap->max) {
        return NULL;
    }
    heap->curr += bytes;
    return (void *) heap->curr - bytes;
}

#ifndef VERIFIED
int main(void)
{
    struct heap *h = malloc(sizeof(struct heap));
    init_heap(h, 1024);

    int i, j;
    int *ptr;

    for (i = 0; i < 1024; i++) {
        printf("%p\n", alloc(h, 1));
    }

    return 0;


    int *x = alloc(h, 0x10);
    printf("%p\n", x);
    int *y = alloc(h, 0xffffffff);
    printf("%p\n", y);
    return 0;

    /* allocate and write 128 ints to the heap */
    for (i = 0; i < 1024; i += 4) {
        ptr = alloc(h, 4);
        *ptr = i;
    }

    /* check written ints correct */
    for (i = 1020; i > 0; i -= 4) {
        j = *ptr;
        if (i != j) {
            printf("%d != %d\n",  i, j);
        }
        ptr--;
    }

    /* check heap is full */
    void *null = alloc(h, 1);
    if (null != NULL) {
        printf("null != NULL\n");
    }



    return 0;
}
#endif
