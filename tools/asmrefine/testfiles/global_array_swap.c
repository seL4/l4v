/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned int uint32_t;
typedef unsigned char uint8_t;
typedef unsigned long word_t;

struct blob {
    uint32_t words[2];
};
typedef struct blob blob_t;

enum _bool {
    false = 0,
    true = 1
};

typedef struct range_blob {
    word_t start;
    word_t end;
} range_blob_t;

typedef struct struct_blob {
    word_t index;
    uint8_t data1;
    uint8_t data2;
    uint8_t data3;
    uint8_t data4;
} struct_blob_t;

typedef struct {
    word_t id;
    word_t index;

    range_blob_t index_range;
    range_blob_t free_index_range;

    void *ptr_to_stuff; /* pointer to initial thread's IPC buffer */
    range_blob_t range_in_stuff;
    range_blob_t next_range_in_stuff;

    struct_blob_t list_of_data[192];

    range_blob_t used_part_of_list;
} big_struct_t;

typedef struct toplevel_struct {
    range_blob_t a_range;
    int config_data1;
    int config_data2;

    big_struct_t *things;
} toplevel_struct_t;

int a_modified_global;
int another_global;
extern toplevel_struct_t toplevel;

void modify_toplevel(int x)
{
    toplevel.config_data1 = x;
}

void add_a_thing(int thing_num, int data_num)
{
    if (data_num < 192) {
        toplevel.things[thing_num].list_of_data[data_num].index = 1;
    } else {
        toplevel.things[thing_num].range_in_stuff.end = -1;
    }
}

void update_a_global(int x)
{
    a_modified_global = x;
}

/* small const global array */
typedef int reference_val;

static const reference_val a_reference_array[] = {
    12
};

static int get_num_reference_vals(void)
{
    return sizeof(a_reference_array) / sizeof(reference_val);
}

static reference_val get_reference_val(int i, int extra_param)
{
    reference_val ref = a_reference_array[i];

    if (ref < extra_param) {
        return 0;
    } else {
        return ref;
    }
}


