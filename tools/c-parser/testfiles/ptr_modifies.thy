(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
