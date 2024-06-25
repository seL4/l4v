(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Nondet_Strengthen_Setup
  imports
    Strengthen
    Nondet_No_Fail
    Nondet_VCG
begin

section \<open>Strengthen setup.\<close>

context strengthen_implementation begin

lemma strengthen_hoare [strg]:
  "\<lbrakk>\<And>r s. st F (\<longrightarrow>) (Q r s) (R r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>)"
  by (cases F, auto elim: hoare_strengthen_post)

lemma strengthen_validE_R_cong[strg]:
  "\<lbrakk>\<And>r s. st F (\<longrightarrow>) (Q r s) (R r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, -)"
  by (cases F, auto intro: hoare_strengthen_postE_R)

lemma strengthen_validE_cong[strg]:
  "\<lbrakk>\<And>r s. st F (\<longrightarrow>) (Q r s) (R r s); \<And>r s. st F (\<longrightarrow>) (S r s) (T r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>S\<rbrace>) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>T\<rbrace>)"
  by (cases F, auto elim: hoare_strengthen_postE)

lemma strengthen_validE_E_cong[strg]:
  "\<lbrakk>\<And>r s. st F (\<longrightarrow>) (S r s) (T r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f -, \<lbrace>S\<rbrace>) (\<lbrace>P\<rbrace> f -, \<lbrace>T\<rbrace>)"
  by (cases F, auto elim: hoare_strengthen_postE simp: validE_E_def)

lemma wpfix_strengthen_hoare:
  "\<lbrakk>\<And>s. st (\<not> F) (\<longrightarrow>) (P s) (P' s); \<And>r s. st F (\<longrightarrow>) (Q r s) (Q' r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) (\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>)"
  by (cases F, auto elim: hoare_chain)

lemma wpfix_strengthen_validE_R_cong:
  "\<lbrakk>\<And>s. st (\<not> F) (\<longrightarrow>) (P s) (P' s); \<And>r s. st F (\<longrightarrow>) (Q r s) (Q' r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -) (\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>, -)"
  by (cases F, auto elim: hoare_chainE simp: validE_R_def)

lemma wpfix_strengthen_validE_cong:
  "\<lbrakk>\<And>s. st (\<not> F) (\<longrightarrow>) (P s) (P' s); \<And>r s. st F (\<longrightarrow>) (Q r s) (R r s);
    \<And>r s. st F (\<longrightarrow>) (S r s) (T r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>S\<rbrace>) (\<lbrace>P'\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>T\<rbrace>)"
  by (cases F, auto elim: hoare_chainE)

lemma wpfix_strengthen_validE_E_cong:
  "\<lbrakk>\<And>s. st (\<not> F) (\<longrightarrow>) (P s) (P' s); \<And>r s. st F (\<longrightarrow>) (S r s) (T r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f -, \<lbrace>S\<rbrace>) (\<lbrace>P'\<rbrace> f -, \<lbrace>T\<rbrace>)"
  by (cases F, auto elim: hoare_chainE simp: validE_E_def)

lemma wpfix_no_fail_cong:
  "\<lbrakk>\<And>s. st (\<not> F) (\<longrightarrow>) (P s) (P' s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (no_fail P f) (no_fail P' f)"
  by (cases F, auto elim: no_fail_pre)

lemmas nondet_wpfix_strgs =
    wpfix_strengthen_validE_R_cong
    wpfix_strengthen_validE_E_cong
    wpfix_strengthen_validE_cong
    wpfix_strengthen_hoare
    wpfix_no_fail_cong

end

lemmas nondet_wpfix_strgs[wp_fix_strgs]
    = strengthen_implementation.nondet_wpfix_strgs

end