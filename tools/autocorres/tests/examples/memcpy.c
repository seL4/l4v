/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

void *memcpy(void *dest, void *src, unsigned long size)
{
    unsigned long i;
    /* unsigned char, so it is the same type in the proofs for all architectures */
    unsigned char *d = (unsigned char *)dest, *s = (unsigned char *)src;
    for (i = 0; i < size; i++) {
        d[i] = s[i];
    }
    return dest;
}

int *memcpy_int(int *dest, int *src)
{
    return memcpy(dest, src, sizeof(*dest));
}

struct my_structure {
    char a;
    int i;
    long j;
};

struct my_structure *memcpy_struct(struct my_structure *dest,
                                   struct my_structure *src)
{
    return memcpy(dest, src, sizeof(*dest));
}
