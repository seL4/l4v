/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef _ALLOC_H_
#define _ALLOC_H_

#ifndef NULL
#define NULL ((void *)0)
#endif

/* System word size. */
typedef unsigned long word_t;

/*
 * Allocator memory node.
 *
 * Used as a node in a linked list tracking free memory regions.
 */
struct mem_node {
    word_t size;
    struct mem_node *next;
};

/*
 * Heap object.
 *
 * Contains a pointer to the first node in the chain, and also keeps
 * track of the number of allocations performed, so we know when the
 * entire heap is free.
 */
struct heap {
    word_t num_allocs;
    struct mem_node *head;
};

/* Minimum granuality of the allocator (log2 of number of bytes). */
#define ALLOC_CHUNK_SIZE_BITS 3

/* Minimum alignment that the allocator will return. */
#define DEFAULT_ALIGNMENT_BITS 3

void *alloc(struct heap *heap, word_t size, word_t alignment_bits);

void dealloc(struct heap *heap, void *ptr, word_t size);

void add_mem_pool(struct heap *heap, void *ptr, word_t size);

void init_allocator(struct heap *init_heap, struct mem_node *init_mem_node);

#endif /* _ALLOC_H_ */
