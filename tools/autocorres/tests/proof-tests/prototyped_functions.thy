(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory prototyped_functions
imports "AutoCorres.AutoCorres"
begin

external_file "prototyped_functions.c"
install_C_file "prototyped_functions.c"

autocorres [ts_force option = moo4] "prototyped_functions.c"

context prototyped_functions begin

thm moo1'_def
thm moo2'_def
thm moo3'_def
thm moo4'_def

lemma "moo1' = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (simp add: moo1'_def)

lemma "moo2' = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (simp add: moo2'_def)

lemma "moo3' x = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (simp add: moo3'_def)

lemma "moo4' = oguard (\<lambda>s. UNDEFINED_FUNCTION)"
  by (simp add: moo4'_def)

end

end
