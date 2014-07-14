(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory bugzilla180
imports "../CTranslation"
begin

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
