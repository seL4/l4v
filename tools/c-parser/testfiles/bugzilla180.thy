(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory bugzilla180
imports "CParser.CTranslation"
begin

external_file "bugzilla180.c"
install_C_file "bugzilla180.c"

context "bugzilla180"
begin

thm g_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL g() \<lbrace> \<acute>ret__int = 15 \<rbrace>"
apply vcg
apply simp
done

thm h_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL h() \<lbrace> \<acute>ret__int = 15 \<rbrace>"
apply vcg
apply simp
done

end

end (* theory *)
