(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
