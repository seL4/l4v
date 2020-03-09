(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory builtins
imports "CParser.CTranslation"
begin

external_file "builtins.c"
install_C_file "builtins.c"

context builtins
begin

thm f_body_def
thm g_body_def

lemma "\<Gamma> \<turnstile> \<lbrace> \<acute>i = 3 \<rbrace> Call f_'proc \<lbrace> \<acute>ret__int = 6 \<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule HoarePartial.Catch [where R="\<lbrace> \<acute>ret__int = 6 \<rbrace>"])
  apply (hoare_rule HoarePartial.Seq [where R="{}"])
    apply (hoare_rule HoarePartial.Cond [where P\<^sub>1="{}" and P\<^sub>2="\<lbrace>\<acute>i=3\<rbrace>"])
        apply (simp add: subset_eq word_sless_def word_sle_def)
      apply (hoare_rule HoarePartial.conseq_exploit_pre)
      apply simp
    apply vcg
    apply simp
  apply vcg
apply vcg
done

(* NOTE:

  apply vcg

at the outset generates three sub-goals, last of which is not provable
*)

end
end
