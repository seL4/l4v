(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver345
  imports "CParser.CTranslation"
begin

external_file "jiraver345.c"
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
