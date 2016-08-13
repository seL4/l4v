/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

volatile int reg;

/** DONT_TRANSLATE
    MODIFIES: reg */
int magic(int x) {
  asm volatile ("blah blah": "r"(x));
  return x;
}

/* abort will generate an empty spec "{}" if optimisation is enabled. */
/** MODIFIES:
    FNSPEC abort_spec: "\<Gamma> \<turnstile> {} Call abort_'proc {}" */
void abort(void);

/* Test specs interleaved with function bodies. */
int call_magic(int x) {
  /** GHOSTUPD: "(\<acute>x < 42, id)" */
  return magic(x);
}
