/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/*
 * Triggers a bug relating to combinations of complex bit operations
 * and bodiless functions.
 */

void fr(unsigned long a, unsigned long b, unsigned long *c)
        __attribute__((externally_visible))
        __attribute__((__noreturn__));

unsigned long global;

struct word_struct {
        unsigned long words[2];
};

static inline struct word_struct
gen_struct(unsigned long a, unsigned long b, unsigned long c, unsigned long d) {
    struct word_struct w;

    w.words[0] = 0;
    w.words[1] = 0;
    w.words[1] |= (a & 0xfffffff8) >> 0;
    w.words[1] |= (b & 0x1) << 1;
    w.words[1] |= (c & 0x1) << 0;
    w.words[0] |= (d & 0xfffffff8) >> 0;

    return w;
}

void
frw(int x)
{
    if (x) {
        fr(3, 4, &global);
        gen_struct(32, 53, 23, 543);
    } else {
        fr(1, 2, (void *)0);
        gen_struct(1, 2, 3, 4);
    }
}

void call_fr(void)
{
    fr(3, 4, &global);
    fr(3, 4, &global);
}

