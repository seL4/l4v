(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver345
  imports "../CTranslation"
begin

  install_C_file "jiraver345.c"

context jiraver345
begin

thm good_body_def
thm bad_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> \<acute>p = Ptr 0 \<rbrace> \<acute>ret__int :== CALL good(\<acute>p) \<lbrace> \<acute>ret__int = 0 \<rbrace>"
apply vcg
apply simp
done

lemma "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL bad(Ptr 0) \<lbrace> \<acute>ret__int = 0 \<rbrace>"
apply vcg
apply simp
done

end

end
