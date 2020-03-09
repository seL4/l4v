/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int global;
void foo(void)
{
  void bar(void);
  bar();
}

/** FNSPEC
      some_external_spec: "\<Gamma> \<turnstile> {} Call some_external_'proc {}"
*/
int some_external(void);
