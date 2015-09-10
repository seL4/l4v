(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory shortcircuit
imports "../CTranslation"
begin

install_C_file "shortcircuit.c"


context shortcircuit
begin

  thm f_body_def
  thm deref_body_def
  thm test_deref_body_def
  thm imm_deref_body_def
  thm simple_body_def
  thm condexp_body_def

lemma semm: "\<Gamma> \<turnstile> \<lbrace> \<acute>p = NULL \<rbrace> Call test_deref_'proc \<lbrace> \<acute>ret__int = 0 \<rbrace>"
apply vcg
apply simp
done

lemma condexp_semm:
  "\<Gamma> \<turnstile> \<lbrace> \<acute>i = 10 & \<acute>ptr = NULL & \<acute>ptr2 = NULL \<rbrace>
                    Call condexp_'proc
                  \<lbrace> \<acute>ret__int = 23 \<rbrace>"
apply vcg
apply (simp add: word_sless_def word_sle_def)
done

end (* context *)

end (* theory *)
