(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory variable_munge
imports "CParser.CTranslation"
begin

external_file "variable_munge.c"
install_C_file "variable_munge.c"

context variable_munge_global_addresses
begin

thm f_body_def
thm g_body_def
thm h_body_def
thm j_body_def
thm bar_body_def
thm qux_body_def

end

lemma  (in variable_munge_global_addresses) j_test1:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL j(255) \<lbrace> \<acute>ret__int = 0 \<rbrace>"
apply vcg
apply simp
done

lemma (in variable_munge_global_addresses) j_test2:
  "\<Gamma> \<turnstile> \<lbrace> True \<rbrace> \<acute>ret__int :== CALL j(-200) \<lbrace> \<acute>ret__int = -400 \<rbrace>"
apply vcg
apply simp
done

end
