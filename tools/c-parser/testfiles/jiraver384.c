/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
