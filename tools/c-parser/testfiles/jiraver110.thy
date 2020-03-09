(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver110
imports "CParser.CTranslation"
begin

external_file "jiraver110.c"
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
