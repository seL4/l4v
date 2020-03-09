/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned int x;

void f(unsigned int n)
{
  while (x < n)
    /** INV: "\<lbrace> (x_addr::32 word ptr) = c \<rbrace>" */
    x = x + n;
}

