(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory signedoverflow
imports "CParser.CTranslation"
begin

external_file "signedoverflow.c"
install_C_file "signedoverflow.c"

context signedoverflow
begin

thm f_body_def

(* painful lemma about sint and word arithmetic results...
lemma j0: "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> Call f_'proc \<lbrace> \<acute>ret__int = 0 \<rbrace>"
apply vcg
apply simp_all
apply auto
*)

thm g_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL g(1) \<lbrace> \<acute>ret__int = - 1 \<rbrace>"
apply vcg
apply (simp add: word_sle_def)
done

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL g(- 2147483648) \<lbrace> \<acute>ret__int = - 1 \<rbrace>"
apply vcg
apply (simp add: word_sle_def)
done

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL g(- 2147483647) \<lbrace> \<acute>ret__int = 2147483647 \<rbrace>"
apply vcg
apply (simp add: word_sle_def)
done

end (* context *)

end (* theory *)
