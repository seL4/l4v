/*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* External functions, DONT_TRANSLATE or undefined in C, but with MODIFIES. */

int x, y;

/* does not change any state */
/** MODIFIES: */
unsigned read_reg(unsigned r);

/* may change machine state */
/** MODIFIES: [*] */
void write_reg(unsigned r, unsigned v);

/* may change global variable x */
/** MODIFIES: x */
int update_x(int a);

/** DONT_TRANSLATE */
/** MODIFIES: [*] */
static inline void tick(void)
{
    __asm__ volatile("tick" ::: "memory");
}

/* not an external function, because FNSPEC sets the body */
/** MODIFIES:
    FNSPEC magic_spec: "\<forall>s. \<Gamma> \<turnstile> {s} Call magic_'proc \<lbrace> \<acute>ret__int = 42 \<rbrace>" */
int magic(void);

/* A function that uses external functions without body */
unsigned swap_reg(unsigned r, unsigned v)
{
    unsigned old = read_reg(r);
    write_reg(r, v);
    return old;
}

/* A function that uses external functions with DONT_TRANSLATE */
int bump(int a)
{
    y = a;
    tick();
    return update_x(a);
}
