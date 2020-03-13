(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory multi_deref
imports "CParser.CTranslation"
begin

external_file "multi_deref.c"
install_C_file "multi_deref.c"

context multi_deref_global_addresses begin

thm f_body_def   (* only 1 C_Guard; see JIRA VER-85 *)
thm g_body_def   (* 2 C_Guards, one per deref; see JIRA VER-152 *)

ML \<open>

val th = @{thm g_body_def}
val t = Thm.concl_of th
fun incifGuard (@{const "C_Guard"}) i = i + 1
  | incifGuard _ i = i

\<close>

ML \<open>
  fold_aterms incifGuard t 0 = 2 orelse
  OS.Process.exit OS.Process.failure
\<close>

end

end
