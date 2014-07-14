(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory analsignedoverflow
imports "../CTranslation"
begin

declare [[anal_integer_conversion=true]]
install_C_file "analsignedoverflow.c"

context analsignedoverflow
begin

  thm f_body_def

(*
lemma "\<Gamma> \<turnstile> \<lbrace> c = sint \<acute>c & c \<le> 117 \<rbrace> \<acute>ret__int :== CALL f()
           \<lbrace> sint \<acute>ret__int = c + 10 \<rbrace>"
apply vcg
apply (simp add: word_sle_def)
urk
*)

end

end
