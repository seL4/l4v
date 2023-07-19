(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_Sat
  imports
    Trace_Monad
    WPSimp
begin

section \<open>Satisfiability\<close>

text \<open>
  The dual to validity: an existential instead of a universal quantifier for the post condition.
  In refinement, it is often sufficient to know that there is one state that satisfies a condition.\<close>
definition exs_valid ::
  "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b) tmonad \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<exists>\<lbrace>_\<rbrace>") where
  "\<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (\<exists>(rv, s') \<in> mres (f s). Q rv s')"

text \<open>The above for the exception monad\<close>
definition ex_exs_validE ::
  "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'e + 'b) tmonad \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace> _ \<exists>\<lbrace>_\<rbrace>, \<lbrace>_\<rbrace>") where
  "\<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace> \<equiv> \<lbrace>P\<rbrace> f  \<exists>\<lbrace>\<lambda>rv. case rv of Inl e \<Rightarrow> E e | Inr v \<Rightarrow> Q v\<rbrace>"


subsection \<open>Set up for @{method wp}\<close>

definition exs_postcondition where
  "exs_postcondition P f \<equiv> \<lambda>a b. \<exists>(rv, s) \<in> f a b. P rv s"

lemma exs_valid_is_triple[wp_trip]:
  "exs_valid P f Q = triple_judgement P f (exs_postcondition Q (\<lambda>s f. mres (f s)))"
  by (simp add: triple_judgement_def exs_postcondition_def exs_valid_def)


subsection \<open>Rules\<close>

lemma exs_hoare_post_imp:
  "\<lbrakk>\<And>r s. Q r s \<Longrightarrow> R r s; \<lbrace>P\<rbrace> a \<exists>\<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> a \<exists>\<lbrace>R\<rbrace>"
  unfolding exs_valid_def by blast

lemma use_exs_valid:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>; P s \<rbrakk> \<Longrightarrow> \<exists>(r, s') \<in> mres (f s). Q r s'"
  by (simp add: exs_valid_def)

lemma exs_valid_weaken_pre[wp_pre]:
  "\<lbrakk> \<lbrace>P'\<rbrace> f \<exists>\<lbrace>Q\<rbrace>; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>"
  by (clarsimp simp: exs_valid_def)

lemma exs_valid_chain:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>; \<And>s. R s \<Longrightarrow> P s; \<And>r s. Q r s \<Longrightarrow> S r s \<rbrakk> \<Longrightarrow> \<lbrace>R\<rbrace> f \<exists>\<lbrace>S\<rbrace>"
  by (fastforce simp: exs_valid_def Bex_def)

lemma exs_valid_assume_pre:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<exists>\<lbrace>Q\<rbrace>"
  by (fastforce simp: exs_valid_def)

lemma exs_valid_bind[wp_split]:
  "\<lbrakk> \<And>rv. \<lbrace>B rv\<rbrace> g rv \<exists>\<lbrace>C\<rbrace>; \<lbrace>A\<rbrace> f \<exists>\<lbrace>B\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>A\<rbrace> f >>= (\<lambda>rv. g rv) \<exists>\<lbrace>C\<rbrace>"
  apply atomize
  apply (clarsimp simp: exs_valid_def bind_def2 mres_def)
  apply (drule spec, drule(1) mp, clarsimp)
  apply (drule spec2, drule(1) mp, clarsimp)
  apply (simp add: image_def bex_Un)
  apply (strengthen subst[where P="\<lambda>x. x \<in> f s" for s, mk_strg I _ E], simp)
  apply (fastforce elim: rev_bexI)
  done

lemma exs_valid_return[wp]:
  "\<lbrace>Q v\<rbrace> return v \<exists>\<lbrace>Q\<rbrace>"
  by (clarsimp simp: exs_valid_def return_def mres_def)

lemma exs_valid_select[wp]:
  "\<lbrace>\<lambda>s. \<exists>r \<in> S. Q r s\<rbrace> select S \<exists>\<lbrace>Q\<rbrace>"
  apply (clarsimp simp: exs_valid_def select_def mres_def)
  apply (auto simp add: image_def)
  done

lemma exs_valid_get[wp]:
  "\<lbrace>\<lambda>s. Q s s\<rbrace> get \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: exs_valid_def get_def mres_def)

lemma exs_valid_gets[wp]:
  "\<lbrace>\<lambda>s. Q (f s) s\<rbrace> gets f \<exists>\<lbrace>Q\<rbrace>"
  by (clarsimp simp: gets_def) wp

lemma exs_valid_put[wp]:
  "\<lbrace>Q v\<rbrace> put v \<exists>\<lbrace>Q\<rbrace>"
  by (clarsimp simp: put_def exs_valid_def mres_def)

lemma exs_valid_fail[wp]:
  "\<lbrace>\<lambda>s. False\<rbrace> fail \<exists>\<lbrace>Q\<rbrace>"
  unfolding fail_def exs_valid_def
  by simp

lemma exs_valid_state_assert[wp]:
    "\<lbrace> \<lambda>s. Q () s \<and> G s \<rbrace> state_assert G \<exists>\<lbrace> Q \<rbrace>"
  by (clarsimp simp: state_assert_def exs_valid_def get_def
           assert_def bind_def2 return_def mres_def)

lemmas exs_valid_guard = exs_valid_state_assert

lemma exs_valid_condition[wp]:
  "\<lbrakk> \<lbrace>P\<rbrace> l \<exists>\<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> r \<exists>\<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. (C s \<and> P s) \<or> (\<not> C s \<and> P' s)\<rbrace> condition C l r \<exists>\<lbrace>Q\<rbrace>"
  by (clarsimp simp: condition_def exs_valid_def split: sum.splits)

end