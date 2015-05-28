(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_struct_array
imports "../CTranslation"
begin

install_C_file "parse_struct_array.c"

term "globk2_'"

print_locale parse_struct_array_global_addresses

context parse_struct_array_global_addresses
begin

  thm f_body_def
  thm g_body_def
  thm h_body_def
  thm ts20110511_1_body_def
  thm ts20110511_2_body_def

ML {*
  val bthm = @{thm "ts20110511_1_body_def"}
  val b_t = Thm.concl_of bthm
  val cs = Term.add_consts b_t []
*}

ML {* member op= (map #1 cs) "CProof.strictc_errortype.C_Guard" orelse
      OS.Process.exit OS.Process.failure *}

end

end
