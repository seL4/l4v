(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver434
  imports "../CTranslation"

begin

install_C_file "jiraver434.c"

context jiraver434
begin

thm useContext_body_def
term "r2_C_update"
ML {*
  val Const(nm, ty) = @{term "ucptr_'"}
  val (d, r) = TermsTypes.dom_rng ty
  val (pointedTo_tyname, []) = dest_Type (TermsTypes.dest_ptr_ty r)
  val basename = List.last (String.fields (fn c => c = #".") pointedTo_tyname)
  val _ = basename = NameGeneration.mkAnonStructName 1 orelse
          raise Fail "anonymous struct has unexpected name"
*}

end (* context *)

end
