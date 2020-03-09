(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory spec_annotated_fn
imports "CParser.CTranslation"
begin

declare sep_conj_ac [simp add]

external_file "spec_annotated_fn.c"
install_C_file "spec_annotated_fn.c"


print_locale spec_annotated_fn
print_locale Square_spec

thm Square_spec_def

context spec_annotated_fn
begin

thm Square_body_def
thm Square_impl
thm Square_spec_def
thm \<Gamma>_def
thm f_spec_def
thm f_body_def

end

lemma (in Square_spec) foo:
  shows "\<Gamma> \<turnstile> \<lbrace> T \<rbrace> \<acute>ret__unsigned :== CALL Square(4) \<lbrace> \<acute>ret__unsigned = 16 \<rbrace> "
apply vcg
apply simp
done

lemma (in spec_annotated_fn)
shows "\<forall>n. \<Gamma> \<turnstile> \<lbrace> \<acute>n = n \<rbrace> \<acute>ret__unsigned :== PROC Square(\<acute>n)
               \<lbrace>\<acute>ret__unsigned = n * n \<rbrace>"
apply vcg
done

lemma (in spec_annotated_fn)
shows "\<forall>n. \<Gamma> \<turnstile> \<lbrace> \<acute>n = n \<rbrace> \<acute>ret__unsigned :== PROC f(\<acute>n) \<lbrace> \<acute>ret__unsigned = n * n \<rbrace>"
apply vcg
apply clarsimp
apply (simp add: mex_def meq_def)
done

end
