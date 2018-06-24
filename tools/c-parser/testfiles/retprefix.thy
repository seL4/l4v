(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory retprefix
imports "CParser.CTranslation"
begin

external_file "retprefix.c"
install_C_file "retprefix.c"

context retprefix
begin

thm f_body_def
thm g_body_def
thm h_body_def
thm i_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>x :== CALL h() \<lbrace> \<acute>x = 6 \<rbrace>"
by vcg simp

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>x :== CALL i() \<lbrace> \<acute>x = 6 \<rbrace>"
by vcg simp

end (* context *)

end (* theory *)
