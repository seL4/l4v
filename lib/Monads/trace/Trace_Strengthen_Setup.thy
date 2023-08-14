(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_Strengthen_Setup
  imports
    Strengthen
    Trace_No_Fail
    Trace_RG
begin

section \<open>Strengthen setup.\<close>

context strengthen_implementation begin

lemma strengthen_hoare[strg]:
  "\<lbrakk>\<And>r s. st F (\<longrightarrow>) (Q r s) (R r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>)"
  by (cases F, auto elim: hoare_strengthen_post)

lemma strengthen_validE_R_cong[strg]:
  "\<lbrakk>\<And>r s. st F (\<longrightarrow>) (Q r s) (R r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, -)"
  by (cases F, auto intro: hoare_post_imp_R)

lemma strengthen_validE_cong[strg]:
  "\<lbrakk>\<And>r s. st F (\<longrightarrow>) (Q r s) (R r s); \<And>r s. st F (\<longrightarrow>) (S r s) (T r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>S\<rbrace>) (\<lbrace>P\<rbrace> f \<lbrace>R\<rbrace>, \<lbrace>T\<rbrace>)"
  by (cases F, auto elim: hoare_post_impErr)

lemma strengthen_validE_E_cong[strg]:
  "\<lbrakk>\<And>r s. st F (\<longrightarrow>) (S r s) (T r s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace> f -, \<lbrace>S\<rbrace>) (\<lbrace>P\<rbrace> f -, \<lbrace>T\<rbrace>)"
  by (cases F, auto elim: hoare_post_impErr simp: validE_E_def)

lemma strengthen_validI[strg]:
  "\<lbrakk>\<And>r s0 s. st F (\<longrightarrow>) (Q r s0 s) (Q' r s0 s)\<rbrakk>
   \<Longrightarrow> st F (\<longrightarrow>) (\<lbrace>P\<rbrace>,\<lbrace>G\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>Q\<rbrace>) (\<lbrace>P\<rbrace>,\<lbrace>G\<rbrace> f \<lbrace>R\<rbrace>,\<lbrace>Q'\<rbrace>)"
  by (cases F, auto elim: validI_strengthen_post)

end

end