/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int f(int m, int n)
{
  int i;
  i = m;
  /** SPEC: "\<tau> . \<lbrace> \<tau>. \<acute>i = \<^bsup>\<sigma> \<^esup>m \<rbrace>" */
  m = n;
  n = i;
  /** END-SPEC: "\<lbrace> \<acute>m = \<^bsup>\<tau>\<^esup>n \<and> \<acute>n = \<^bsup>\<tau>\<^esup>i \<rbrace>" */
  return m + n;
}


