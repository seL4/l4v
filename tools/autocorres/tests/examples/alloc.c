/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#include "alloc.h"

/* Disable "printk" error messages. */
#define printk(x...)

/*
 * Ensure condition "x" is true.
 */
#define assert(x) \
    do { if (!(x)) { for (;;); } } while (0)

/* Is the given value aligned to the given alignment? */
#define IS_ALIGNED(x, val) (((x) % (1UL << val)) == 0UL)

/* Align "val" up to the next "2 ** align_bits" boundary. */
static word_t
align_up(word_t val, word_t align_bits)
{
    assert(align_bits < 32UL);
    return (val + ((1UL << align_bits) - 1UL)) & (~((1UL << align_bits) - 1UL));
}

/* Return the maximum of "a" and "b". */
static word_t
max(word_t a, word_t b)
{
    if (a >= b)
        return a;
    return b;
}

/*
 * This simple allocator uses a linked list of "mem_nodes", each which
 * contain a size (indicating that the 'size' bytes from the beginning
 * of the mem_node are free, other than containing the mem_node itself),
 * and a pointer to the next. The list of "mem_nodes" are in sorted
 * order by their virtual address.
 *
 * We additionally have an initial "dummy" mem_node that begins the list
 * of size 0. This is to make the code simpler by each node having
 * a previous node. The typical method of dealing with this (taking
 * a pointer the previous node's next pointer) unfortunately does not
 * work due to limitations in the verification framework. (Pointers
 * can't be taken to a field of a struct.)
 *
 * To allocate, we find a mem_node which contains a valid range and
 * allocate the range out of the mem_node. This may completely use up
 * the mem_node (in which case, it is taken out of the list), be
 * allocated from the start or end of the mem_node (in which case it is
 * adjusted/moved), or be allocated from the middle of the mem_node (in
 * which case, we end up with one more mem_node than we begun with).
 *
 * Free'ing is the reverse process, ensuring that we correctly merge
 * mem_nodes as required.
 */

/* Allocate a chunk of memory. */
void *
alloc(struct heap *heap, word_t size, word_t alignment_bits)
{
    assert(size > 0);
    assert(alignment_bits < 32);

    struct mem_node *prev = heap->head;
    struct mem_node *current = prev->next;

    /* Round size and alignment up to ALLOC_CHUNK_SIZE_BITS */
    size = align_up(size, ALLOC_CHUNK_SIZE_BITS);
    alignment_bits = max(alignment_bits, ALLOC_CHUNK_SIZE_BITS);

    while (current != NULL) {
        /* Calculate the bounds of this region of memory. */
        word_t node_start = (word_t)current;
        word_t node_end = node_start + current->size - 1;
        assert(node_start < node_end);
        assert(IS_ALIGNED(node_end + 1, ALLOC_CHUNK_SIZE_BITS));

        /* Calculate the bounds of our desired memory region,
         * noting that we may overflow in either calculation. */
        word_t desired_start = align_up(node_start, alignment_bits);
        word_t desired_end = desired_start + size - 1;

        /* If the desired range (after alignment and size changes)
         * fits within this node, then allocate it. */
        if (desired_start >= node_start
                && desired_end <= node_end
                && desired_start < desired_end) {
            /* If we have space after the allocation, create a new node
             * covering the area. */
            if (desired_end != node_end) {
                assert(node_end - desired_end >= ALLOC_CHUNK_SIZE_BITS);
                struct mem_node *new_node = (struct mem_node *)(desired_end + 1);
                new_node->size = node_end - desired_end;
                new_node->next = current->next;
                current->next = new_node;
            }

            /* If we have space before the allocation, update the node.
             * Otherwise, remove it. */
            if (desired_start != node_start) {
                current->size = desired_start - node_start;
            } else {
                prev->next = current->next;
            }

            /* Return the allocation. */
            heap->num_allocs++;
            return (void *)desired_start;
        }

        prev = current;
        current = current->next;
    }

    return NULL;
}

/* Free a chunk of memory. */
void
dealloc(struct heap *heap, void *ptr, word_t size)
{
    assert(size > 0);
    assert(ptr != NULL);

    struct mem_node *prev = heap->head;
    struct mem_node *current = prev->next;
    struct mem_node *new = (struct mem_node *)ptr;

    /* Round size and alignment up to ALLOC_CHUNK_SIZE_BITS */
    size = align_up(size, ALLOC_CHUNK_SIZE_BITS);

    /* Find our position in the list. */
    while ((word_t)current < (word_t)ptr && (current != NULL)) {
        prev = current;
        current = current->next;
    }

    /* Determine if we should merge with previous, or add a new node. */
    if ((word_t)prev + prev->size == (word_t)new) {
        prev->size += size;
        new = prev;
    } else {
        new->size = size;
        prev->next = new;
    }

    /* Determine if we should merge the next with the new. */
    if ((word_t)new + new->size == (word_t)current) {
        new->size += current->size;
        new->next = current->next;
    } else {
        new->next = current;
    }

    /* Track deallocation. */
    heap->num_allocs--;
}

/* Add a pool of memory to the given allocator. */
void
add_mem_pool(struct heap *heap, void *ptr, word_t size)
{
    printk("Adding memory pool %lx--%lx\n",
            (word_t)ptr, (word_t)ptr + size);
    dealloc(heap, ptr, size);
    heap->num_allocs++;
}

/* Setup the initial allocator. */
void
init_allocator(struct heap *init_heap, struct mem_node *init_mem_node)
{
    init_heap->head = init_mem_node;
    init_heap->head->size = 0;
    init_heap->head->next = NULL;
}


