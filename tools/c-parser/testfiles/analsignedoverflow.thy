(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory analsignedoverflow
imports "CParser.CTranslation"
begin

external_file "analsignedoverflow.c"

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
