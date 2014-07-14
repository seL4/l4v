/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

void *memcpy(void *dest, void *src, unsigned int size) {
    /** AUXUPD: "(True,  id)" */
    unsigned int i;
    char *d = (char*)dest, *s = (char*)src;
    for (i = 0; i < size; i++) {
        d[i] = s[i];
    }
    return dest;
}
