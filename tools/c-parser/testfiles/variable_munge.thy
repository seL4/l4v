(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
