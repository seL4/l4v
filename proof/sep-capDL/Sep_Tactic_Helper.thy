(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Sep_Tactic_Helper
imports
  "SepTactics.Hoare_Sep_Tactics"
  "Sep_Algebra.MonadSep"
begin

lemma no_exception_conjE:
  "\<lbrakk>\<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>, -; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>r s. Q r s \<and> Q' r s\<rbrace>, \<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def validE_R_def valid_def split: sum.splits)

definition
  sep_any :: "('b \<Rightarrow> 'c \<Rightarrow> ('a \<Rightarrow> bool)) \<Rightarrow> ('b \<Rightarrow> ('a \<Rightarrow> bool))" where
  "sep_any m \<equiv> (\<lambda>p s. \<exists>v. (m p v) s)"

lemma sep_any_imp[sep_cancel]: "(m p e) s \<Longrightarrow> sep_any m p s"
  by (fastforce simp: sep_any_def)

end
