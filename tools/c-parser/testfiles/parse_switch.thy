(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
