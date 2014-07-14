/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

typedef unsigned long uint32_t;
typedef uint32_t vptr_t;

struct cap {
    uint32_t words[2];
};
typedef struct cap cap_t;

struct mdb_node {
    uint32_t words[2];
};
typedef struct mdb_node mdb_node_t;

struct create_ipcbuf_frame_ret {
    cap_t  ipcbuf_cap;
    vptr_t ipcbuf_vptr;
};
typedef struct create_ipcbuf_frame_ret create_ipcbuf_frame_ret_t;

create_ipcbuf_frame_ret_t
create_ipcbuf_frame(void)
{
    cap_t  cap;
    vptr_t vptr;
    /* If I comment out the line below, it works! */
    return (create_ipcbuf_frame_ret_t){ cap, vptr };
}

/* And if I only comment out the completely unrelated struct */
/* below (and keep the line above), it works as well!        */
struct cte {
    cap_t cap;
    mdb_node_t cteMDBNode;
};
