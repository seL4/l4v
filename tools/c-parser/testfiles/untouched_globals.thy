(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory untouched_globals
imports "CParser.CTranslation"
begin

external_file "untouched_globals.c"

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
