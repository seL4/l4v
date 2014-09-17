/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct s {
    unsigned long x;
};

struct word_struct {
        unsigned long words[2];
};

struct sc {
    struct s cap;
    struct word_struct ws;
};

static inline unsigned __attribute__((__const__))
    bb(struct word_struct word_struct) {
        return (word_struct.words[0] & 0xfffffff8) << 0;
    }

static inline struct s __attribute__((__const__))
    cncn(void) {
        struct s x;
        x.x = 0;
        return x;
    }

static inline unsigned __attribute__((__const__))
    aa(struct word_struct word_struct) {
            return (word_struct.words[1] & 0xfffffff8) << 0;
    }

static inline void
ff(struct word_struct *mdb_node_ptr, unsigned v) {
        mdb_node_ptr->words[1] &= ~0xfffffff8;
            mdb_node_ptr->words[1] |= (v >> 0) & 0xfffffff8;
}

static inline struct word_struct __attribute__((__const__))
    cc(struct word_struct word_struct, unsigned v) {
            word_struct.words[0] &= ~0xfffffff8;
                word_struct.words[0] |= (v >> 0) & 0xfffffff8;
                    return word_struct;
    }

static inline void
ee(struct word_struct *mdb_node_ptr, unsigned v) {
        mdb_node_ptr->words[0] &= ~0xfffffff8;
            mdb_node_ptr->words[0] |= (v >> 0) & 0xfffffff8;
}

static inline struct word_struct
mk_word_struct(unsigned long a, unsigned long b, unsigned long c, unsigned long d) {
    struct word_struct w;

    w.words[0] = 0;
    w.words[1] = 0;
    w.words[1] |= (a & 0xfffffff8);
    w.words[1] |= (b & 0x1) << 1;
    w.words[1] |= (c & 0x1);
    w.words[0] |= (d & 0xfffffff8);

    return w;
}


void
do_call(struct s newCap, struct sc *s, struct sc *d) {
    struct word_struct the_ws;
    unsigned pp, np;
    ; ;
    the_ws = s->ws;
    d->cap = newCap;
    s->cap = cncn();
    d->ws = the_ws;
    s->ws = mk_word_struct(0, 0, 0, 0);

    pp = bb(the_ws);
    if(pp)
        ff(&((struct sc *)(pp))->ws, ((unsigned int)d));

    np = aa(the_ws);
    if(np)
        ee(&((struct sc *)(np))->ws, ((unsigned int)d));
}


