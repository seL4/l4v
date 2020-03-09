(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_switch
imports "CParser.CTranslation"
begin

external_file "parse_switch.c"
install_C_file "parse_switch.c"

context parse_switch_global_addresses
begin

thm f_body_def
thm g_body_def
thm h_body_def
thm j_body_def
thm k_body_def

ML \<open>
  val kthm = @{thm k_body_def}
  val k_t = Thm.concl_of kthm
  val cs = Term.add_consts k_t []
\<close>

ML \<open>
  member (=) (map #1 cs) "CProof.strictc_errortype.C_Guard" orelse
  OS.Process.exit OS.Process.failure
\<close>

end

end
