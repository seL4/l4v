/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* asm statements that are accepted */
typedef unsigned long word_t;

struct s { word_t a; unsigned int b[2]; };

typedef enum _irq_t { irq_a, irq_b } irq_t;

word_t good(word_t x, unsigned int u, unsigned short h, struct s *p, int i,
            irq_t irq)
{
  word_t v;
  asm volatile("mrs %0, tpidr_el1" : "=r"(v));
  asm volatile("msr tpidr_el1, %0" : : "r"(x));
  asm volatile("msr tpidr_el1, %0" : : "r"(u));            /* narrower: cast */
  asm volatile("msr tpidr_el1, %0" : : "r"(h));            /* narrower: cast */
  asm volatile("msr tpidr_el1, %0" : : "r"(i));            /* signed: cast */
  asm volatile("msr tpidr_el1, %0" : : "r"(p));            /* pointer */
  asm volatile("msr tpidr_el1, %0" : : "r"(p->b));         /* array decays to pointer */
  asm volatile("msr tpidr_el1, %0" : : "i"(4));            /* immediate constant */
  asm volatile("msr tpidr_el1, %0" : : "r"(irq));          /* enum */
  asm volatile("msr tpidr_el1, %0" : : "r"((word_t)irq));  /* cast to typedef */
  asm volatile("msr tpidr_el1, %0" : : "r"((word_t)p));    /* cast to typedef */
  asm volatile("msr tpidr_el1, %0" : : "r"((word_t *)x));  /* cast to typedef ptr */
  asm volatile("mrs %0, tpidr_el1" : "=r"(p->a));          /* field lvalue */
  asm volatile("dmb sy" : : : "memory");
  /* two inputs */
  asm volatile("dc civac, %0; dc civac, %1" : : "r"(x), "r"(p));
  /* output + three inputs */
  asm volatile("add %0, %1, %2" : "=r"(v) : "r"(x), "r"((word_t)u), "i"(8));
  return v;
}
