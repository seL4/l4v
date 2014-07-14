(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver110
imports "../CTranslation"
begin

install_C_file "jiraver110.c"

context jiraver110
begin

thm f_body_def

(* this should be provable *)
lemma shouldbetrue:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL f(0) \<lbrace> \<acute>ret__int = 1 \<rbrace>"
apply vcg
apply simp
(* when this is provable, more will be required here *)
done

end

end
