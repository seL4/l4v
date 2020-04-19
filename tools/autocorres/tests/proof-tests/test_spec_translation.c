/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

volatile int reg;

/** DONT_TRANSLATE
    MODIFIES: reg */
int magic(int x)
{
    asm volatile("blah blah": "r"(x));
    return x;
}

/* abort will generate an empty spec "{}" if optimisation is enabled. */
/** MODIFIES:
    FNSPEC abort_spec: "\<Gamma> \<turnstile> {} Call abort_'proc {}" */
void abort(void);

/* Test specs interleaved with function bodies. */
int call_magic(int x)
{
    /** GHOSTUPD: "(\<acute>x < 42, id)" */
    return magic(x);
}
