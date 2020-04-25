/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/**
 RELSPEC "{ (s,t). \<^bsup>s\<^esup>x < \<^bsup>t\<^esup>ret__int }"
*/
int f(int x)
{
  return x + 2;
}

/**
 RELSPEC "{ (s,t). \<^bsup>s\<^esup>glob < \<^bsup>t\<^esup>ret__int }"
*/
int g(void);
