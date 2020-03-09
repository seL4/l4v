/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef long word_t;
typedef long tcb_t;

/**
  DONT_TRANSLATE
  */
__attribute__((noreturn))
static inline void
fastpath_restore(word_t badge, word_t msgInfo, tcb_t *cur_thread)
{
    register word_t r0 asm ("r0") = badge;
    register word_t r1 asm ("r1") = msgInfo;
    asm volatile (
            "add sp, %[cur_thread], %[offset]\n\t" /* Point to LR_svc */
            "ldmdb sp, {r2-lr}^\n\t"
            "rfeia sp\n\t"
        :
        : [offset] "i" (PT_LR_svc),
          [cur_thread] "r" (cur_thread),
          "r"(r0), "r"(r1)
        : "memory" );
}
