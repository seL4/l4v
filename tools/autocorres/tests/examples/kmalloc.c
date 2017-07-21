/* this is a -*- c -*- file */
/*
 * @TAG(OTHER_BSD)
 */

/* ********************************************************************
 *
 * Copyright (C) 2002, 2003-2004,  Karlsruhe University
 *   Original authors
 *
 * Copyright (C) 2009-2012, NICTA
 *   Translation to C for verification experiments.
 *
 * Description:   very simple kernel memory allocator
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 ******************************************************************* */

typedef unsigned int u64_t;
typedef unsigned int u32_t;
typedef unsigned short u16_t;
typedef unsigned char u8_t;

typedef signed int s64_t;
typedef signed int s32_t;
typedef signed short s16_t;
typedef signed char s8_t;

typedef u32_t word_t;


typedef void* addr_t;


word_t *kmem_free_list;

void init (void * start, void * end);
void free (void * address, word_t size);

void * alloc (word_t size);
void * alloc_aligned (word_t size, word_t alignement, word_t mask);



void init(void * start, void * end)
{
    kmem_free_list = 0;

    free(start, (word_t)end - (word_t)start);

}

void free(void * address, word_t size)
{
    word_t* p;
    word_t* prev, *curr;

    size = size >= 1024 ? size : 1024;

    /** AUXUPD: "(True,ptr_retyps (unat \<acute>size div unat KMC) (ptr_val \<acute>address))" */

    for (p = (word_t*)address;
         p < ((word_t*)(((word_t)address) + size - (1024)));
         p = (word_t*) *p)
        *p = (word_t) p + (1024);

    for (prev = (word_t*) &kmem_free_list, curr = kmem_free_list;
         curr && (address > (void *)curr);
         prev = curr, curr = (word_t*) *curr)
    ;

    *prev = (word_t) address; *p = (word_t) curr;
}



void sep_free(void * address, word_t size)
{
    word_t* p;
    word_t* prev, *curr;

    size = size >= 1024 ? size : 1024;

    /** AUXUPD: "(True,ptr_retyp (ptr_coerce \<acute>address::word32 ptr))" */

    for (p = (word_t*)address;
         p < ((word_t*)(((word_t)address) + size - (1024)));
         p = (word_t*) *p)
      {
        *p = (word_t) p + (1024);
        /** AUXUPD: "(True,ptr_retyp (Ptr (ptr_val \<acute>p + 1024)::word32 ptr))" */
      }

    for (prev = (word_t*) &kmem_free_list, curr = kmem_free_list;
         curr && (address > (void *)curr);
         prev = curr, curr = (word_t*) *curr)
    ;

    *prev = (word_t) address; *p = (word_t) curr;
}


void * alloc(word_t size)
{
    word_t* prev;
    word_t* curr;
    word_t* tmp;
    word_t i;

    size = size >= 1024 ? size : 1024;

    for (prev = (word_t*) &kmem_free_list, curr = kmem_free_list;
         curr;
         prev = curr, curr = (word_t*) *curr)
    {
        if (!((word_t) curr & (size - 1)))
        {
            tmp = (word_t*) *curr;
            for (i = 1; tmp && (i < (size / (1024))); i++)
            {

                if ((word_t) tmp != ((word_t) curr + (1024)*i))
                {
                    tmp = 0;
                    break;
                };
                tmp = (word_t*) *tmp;
            }
            if (tmp)
            {

                *prev = (word_t) tmp;


                for (i = 0; i < (size / sizeof(word_t)); i++)
                    curr[i] = 0;

                return curr;
            }
        }
    }

    return 0;
}

void * sep_alloc(word_t size)
{
    word_t* prev;
    word_t* curr;
    word_t* tmp;
    word_t i;

    size = size >= 1024 ? size : 1024;

    for (prev = (word_t*) &kmem_free_list, curr = kmem_free_list;
         curr;
         prev = curr, curr = (word_t*) *curr)
    {
        if (!((word_t) curr & (size - 1)))
        {
            tmp = (word_t*) *curr;
            for (i = 1; tmp && (i < (size / (1024))); i++)
            {

                if ((word_t) tmp != ((word_t) curr + (1024)*i))
                {
                    tmp = 0;
                    break;
                };
                tmp = (word_t*) *tmp;
            }
            if (tmp)
            {

                *prev = (word_t) tmp;


                for (i = 0; i < (size / sizeof(word_t)); i++)
                    {
                    /** AUXUPD: "(ptr_safe (\<acute>curr +\<^sub>p uint \<acute>i) (hrs_htd \<acute>t_hrs),ptr_retyp (\<acute>curr +\<^sub>p uint \<acute>i))"*/
                    curr[i] = 0;
                }

                return curr;
            }
        }
    }

    return 0;
}

void kmalloc_test(word_t size)
{
    void *p;

    p = alloc(size);

    if (!p) return;

    free(p, size);
}

void sep_test(word_t size)
{
    void *p;

    p = sep_alloc(size);

    if (!p) return;

    sep_free(p, size);
}

