(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ptr_modifies
imports "Word_Lib.WordSetup" "CParser.CTranslation"
begin

external_file "ptr_modifies.c"
install_C_file "ptr_modifies.c"

context ptr_modifies
begin
  thm foo_ptr_new_modifies
  thm f_modifies
  thm f_body_def
  thm g_modifies
  thm h_modifies
end

lemma (in f_spec) g_spec:
  "\<forall> i. \<Gamma> \<turnstile> \<lbrace> \<acute>i = i \<rbrace> \<acute>ret__unsigned :== CALL g(\<acute>i) \<lbrace> \<acute>ret__unsigned = i + 4 \<rbrace>"
apply vcg
apply simp
done

end
