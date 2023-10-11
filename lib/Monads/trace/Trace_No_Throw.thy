(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas about no_throw. Usually should have a conclusion "no_throw P m".
   Includes some monad equations that have no_throw as a main assumption.  *)

theory Trace_No_Throw
  imports
    Trace_VCG
begin

section "Basic exception reasoning"

text \<open>
  The predicates @{text no_throw} and @{text no_return} allow us to reason about functions in
  the exception monad that never throw an exception or never return normally.\<close>

definition no_throw :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'e + 'a) tmonad \<Rightarrow> bool" where
  "no_throw P A \<equiv> \<lbrace> P \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_ _. False \<rbrace>"

definition no_return :: "('a \<Rightarrow> bool) \<Rightarrow> ('a, 'b + 'c) tmonad \<Rightarrow> bool" where
  "no_return P A \<equiv> \<lbrace> P \<rbrace> A \<lbrace>\<lambda>_ _. False\<rbrace>,\<lbrace>\<lambda>_ _. True \<rbrace>"

(* Alternative definition of no_throw; easier to work with than unfolding validE. *)
lemma no_throw_def':
  "no_throw P A = (\<forall>s. P s \<longrightarrow> (\<forall>(r, t) \<in> mres (A s). (\<exists>x. r = Inr x)))"
  by (clarsimp simp: no_throw_def validE_def2 split_def split: sum.splits)


subsection \<open>no_throw rules\<close>

lemma no_throw_returnOk[simp]:
  "no_throw P (returnOk a)"
  unfolding no_throw_def
  by wp

lemma no_throw_liftE[simp]:
  "no_throw P (liftE x)"
  by (wpsimp simp: liftE_def no_throw_def validE_def)

lemma no_throw_bindE:
  "\<lbrakk> no_throw A X; \<And>a. no_throw B (Y a); \<lbrace> A \<rbrace> X \<lbrace> \<lambda>_. B \<rbrace>,\<lbrace> \<lambda>_ _. True \<rbrace> \<rbrakk>
   \<Longrightarrow> no_throw A (X >>=E Y)"
  unfolding no_throw_def
  using hoare_validE_cases seqE by blast

lemma no_throw_bindE_simple:
  "\<lbrakk> no_throw \<top> L; \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L >>=E R)"
  using hoareE_TrueI no_throw_bindE by blast

lemma no_throw_handleE_simple:
  "\<lbrakk> \<And>x. no_throw \<top> L \<or> no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle> R)"
  by (fastforce simp: no_throw_def' handleE_def handleE'_def validE_def valid_def bind_def return_def
                      mres_def image_def
                split: sum.splits tmres.splits)

lemma no_throw_handle2:
  "\<lbrakk> \<And>a. no_throw Y (B a); \<lbrace> X \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_. Y \<rbrace> \<rbrakk> \<Longrightarrow> no_throw X (A <handle2> B)"
  by (fastforce simp: no_throw_def' handleE'_def validE_def valid_def bind_def return_def mres_def
                      image_def
                split: sum.splits tmres.splits)

lemma no_throw_handle:
  "\<lbrakk> \<And>a. no_throw Y (B a); \<lbrace> X \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_. Y \<rbrace> \<rbrakk> \<Longrightarrow> no_throw X (A <handle> B)"
  unfolding handleE_def
  by (rule no_throw_handle2)

lemma no_throw_fail[simp]:
  "no_throw P fail"
  by (clarsimp simp: no_throw_def)

lemma handleE'_nothrow_lhs:
  "no_throw \<top> L \<Longrightarrow> no_throw \<top> (L <handle2> R)"
  unfolding no_throw_def
  using handleE'_wp[rotated] by fastforce

lemma handleE'_nothrow_rhs:
  "\<lbrakk> \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle2> R)"
  unfolding no_throw_def
  by (metis hoareE_TrueI no_throw_def no_throw_handle2)

lemma handleE_nothrow_lhs:
  "no_throw \<top> L \<Longrightarrow> no_throw \<top> (L <handle> R)"
  by (metis handleE'_nothrow_lhs handleE_def)

lemma handleE_nothrow_rhs:
  "\<lbrakk> \<And>x. no_throw \<top> (R x) \<rbrakk> \<Longrightarrow> no_throw \<top> (L <handle> R)"
  by (metis no_throw_handleE_simple)

lemma condition_nothrow:
  "\<lbrakk> no_throw \<top> L; no_throw \<top> R \<rbrakk> \<Longrightarrow> no_throw \<top> (condition C L R)"
  by (clarsimp simp: condition_def no_throw_def validE_def2)

lemma no_throw_Inr:
  "\<lbrakk> x \<in> mres (A s); no_throw P A; P s \<rbrakk> \<Longrightarrow> \<exists>y. fst x = Inr y"
  by (fastforce simp: no_throw_def' split: sum.splits)

end