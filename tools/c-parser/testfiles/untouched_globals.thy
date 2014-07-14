(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory untouched_globals
imports "../CTranslation"
begin

declare [[record_globinits=true]]
install_C_file "untouched_globals.c"

context untouched_globals
begin

  thm x_def
  thm x_global_initializer_def
  thm glob1_def
  thm glob1_global_initializer_def
  thm glob2_def
  thm glob2_global_initializer_def
  thm y_global_initializer_def

lemma "x = 0" by (simp add: x_def)

lemma "y_global_initializer = 1" by (unfold y_global_initializer_def, simp)

lemma "c_C glob1 = 0" by (simp add: glob1_def)

lemma "c_C glob2 = 51" by (simp add: glob2_def)

end (* context *)

end (* theory *)
