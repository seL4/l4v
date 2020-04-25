(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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
