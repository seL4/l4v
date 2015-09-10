(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory breakcontinue
imports "../CTranslation"
begin

declare sep_conj_ac [simp add]
install_C_file "breakcontinue.c"

context breakcontinue_global_addresses
begin

thm f_body_def
thm g_body_def
thm h_body_def
thm i_body_def
thm dotest_body_def

lemma h:
  "\<Gamma> \<turnstile> \<lbrace> -10 <=s \<acute>e & \<acute>e <s 0 \<rbrace>
  \<acute>ret__int :== PROC h(\<acute>e)
  \<lbrace> \<acute>ret__int = \<acute>e \<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule HoarePartial.Catch [where R = "\<lbrace> \<acute>ret__int = \<acute>e \<rbrace>"])
  defer
  apply vcg
apply (hoare_rule HoarePartial.conseq
           [where P' = "\<lambda>e. \<lbrace> \<acute>e = e & e <s 0 & -10 <=s e \<rbrace>"
            and Q' = "\<lambda>e. \<lbrace> \<acute>e = e & \<acute>ret__int = e \<rbrace>"
            and A' = "\<lambda>e. \<lbrace> \<acute>e = e & \<acute>ret__int = e \<rbrace>"])
  defer
  apply (simp add: subset_iff)
apply clarsimp
apply (rule_tac R="{}" in HoarePartial.Seq)
  defer
  apply vcg
apply (rule_tac R="\<lbrace> \<acute>e = Z \<rbrace>" in HoarePartial.Seq)
  defer
  apply vcg
apply (rule_tac R = "\<lbrace> \<acute>e = Z & \<acute>global_exn_var = Break \<rbrace>" in HoarePartial.Catch)
  defer
  apply vcg
  apply simp
apply (rule_tac P' = "\<lbrace> \<acute>e = Z & Z <s 0 & -10 <=s Z \<rbrace>"
            and Q' = "\<lbrace> \<acute>e = Z & Z <s 0 & -10 <=s Z \<rbrace> \<inter> - \<lbrace> \<acute>e <s 10 \<rbrace>"
            and A' = "\<lbrace> \<acute>e = Z & \<acute>global_exn_var = Break \<rbrace>"
         in HoarePartial.conseq_no_aux)
  defer
  apply simp
apply (simp add: whileAnno_def)
apply (rule HoarePartialDef.While)
apply vcg
apply (simp add: subset_iff)
done

(* another example where vcg fails, generating impossible sub-goals *)
lemma dotest:
  "\<Gamma> \<turnstile> \<lbrace> \<acute>x = 4 \<rbrace> \<acute>ret__int :== PROC dotest(\<acute>x)
       \<lbrace> \<acute>ret__int = 4 \<rbrace>"
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule HoarePartial.Catch [where R="\<lbrace> \<acute>ret__int = 4 \<rbrace>"])
  apply (hoare_rule HoarePartial.Seq [where R="{}"])
    apply (hoare_rule HoarePartial.Seq [where R="\<lbrace> \<acute>x = 4 \<rbrace>"])
      apply (hoare_rule HoarePartial.Catch [where R="\<lbrace> \<acute>x = 4 & \<acute>global_exn_var = Break \<rbrace>"])
        apply (hoare_rule HoarePartial.Seq [where R="\<lbrace> False \<rbrace>"])
          apply (vcg, simp)
        apply (hoare_rule HoarePartial.conseq_exploit_pre, simp)
      apply (vcg, simp)
    apply vcg
  apply vcg
apply vcg
done

end

end
