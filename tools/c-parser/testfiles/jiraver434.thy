(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver434
  imports "CParser.CTranslation"

begin

external_file "jiraver434.c"
install_C_file "jiraver434.c"

context jiraver434
begin

thm useContext_body_def
term "r2_C_update"
ML \<open>
  val Const(nm, ty) = @{term "ucptr_'"}
  val (d, r) = TermsTypes.dom_rng ty
  val (pointedTo_tyname, []) = dest_Type (TermsTypes.dest_ptr_ty r)
  val basename = List.last (String.fields (fn c => c = #".") pointedTo_tyname)
  val _ = basename = NameGeneration.mkAnonStructName 1 orelse
          raise Fail "anonymous struct has unexpected name"
\<close>

end (* context *)

end
