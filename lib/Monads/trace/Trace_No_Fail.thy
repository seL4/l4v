(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas about the no_fail predicate. *)

theory Trace_No_Fail
  imports
    Trace_In_Monad
    Trace_VCG
    WPSimp
begin

subsection "Non-Failure"

text \<open>
  With the failure result, we can formulate non-failure separately from validity.
  A monad @{text m} does not fail under precondition @{text P}, if for no start
  state that satisfies the precondition it returns a @{term Failed} result.
\<close>
definition no_fail :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) tmonad \<Rightarrow> bool" where
  "no_fail P m \<equiv> \<forall>s. P s \<longrightarrow> Failed \<notin> snd ` (m s)"


subsection \<open>@{method wpc} setup\<close>

lemma no_fail_pre[wp_pre]:
  "\<lbrakk> no_fail P f; \<And>s. Q s \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> no_fail Q f"
  by (simp add: no_fail_def)

lemma wpc_helper_no_fail_final:
  "no_fail Q f \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') (no_fail P f)"
  by (clarsimp simp: wpc_helper_def elim!: no_fail_pre)

wpc_setup "\<lambda>m. no_fail P m" wpc_helper_no_fail_final


subsection \<open>Bundles\<close>

bundle no_pre = hoare_pre [wp_pre del] no_fail_pre [wp_pre del]


subsection \<open>Lemmas\<close>

lemma no_failD:
  "\<lbrakk> no_fail P m; P s \<rbrakk> \<Longrightarrow> Failed \<notin> snd ` m s"
  by (simp add: no_fail_def)

lemma no_fail_modify[wp,simp]:
  "no_fail \<top> (modify f)"
  by (simp add: no_fail_def modify_def get_def put_def bind_def)

lemma no_fail_gets_simp[simp]:
  "no_fail P (gets f)"
  unfolding no_fail_def gets_def get_def return_def bind_def
  by simp

lemma no_fail_gets[wp]:
  "no_fail \<top> (gets f)"
  by simp

lemma no_fail_select[simp]:
  "no_fail \<top> (select S)"
  by (simp add: no_fail_def select_def image_def)

lemma no_fail_alt[wp]:
  "\<lbrakk> no_fail P f; no_fail Q g \<rbrakk> \<Longrightarrow> no_fail (P and Q) (f \<sqinter> g)"
  by (auto simp: no_fail_def alternative_def)

lemma no_fail_return[simp, wp]:
  "no_fail \<top> (return x)"
  by (simp add: return_def no_fail_def)

lemma no_fail_get[simp, wp]:
  "no_fail \<top> get"
  by (simp add: get_def no_fail_def)

lemma no_fail_put[simp, wp]:
  "no_fail \<top> (put s)"
  by (simp add: put_def no_fail_def)

lemma no_fail_when[wp]:
  "(P \<Longrightarrow> no_fail Q f) \<Longrightarrow> no_fail (if P then Q else \<top>) (when P f)"
  by (simp add: when_def)

lemma no_fail_unless[wp]:
  "(\<not>P \<Longrightarrow> no_fail Q f) \<Longrightarrow> no_fail (if P then \<top> else Q) (unless P f)"
  by (simp add: unless_def when_def)

lemma no_fail_fail[simp, wp]:
  "no_fail \<bottom> fail"
  by (simp add: fail_def no_fail_def)

lemma no_fail_assert[simp, wp]:
  "no_fail (\<lambda>_. P) (assert P)"
  by (simp add: assert_def)

lemma no_fail_assert_opt[simp, wp]:
  "no_fail (\<lambda>_. P \<noteq> None) (assert_opt P)"
  by (simp add: assert_opt_def split: option.splits)

lemma no_fail_case_option[wp]:
  assumes f: "no_fail P f"
  assumes g: "\<And>x. no_fail (Q x) (g x)"
  shows "no_fail (if x = None then P else Q (the x)) (case_option f g x)"
  by (clarsimp simp add: f g)

lemma no_fail_if[wp]:
  "\<lbrakk> P \<Longrightarrow> no_fail Q f; \<not>P \<Longrightarrow> no_fail R g \<rbrakk> \<Longrightarrow> no_fail (if P then Q else R) (if P then f else g)"
  by simp

lemma no_fail_apply[wp]:
  "no_fail P (f (g x)) \<Longrightarrow> no_fail P (f $ g x)"
  by simp

lemma no_fail_undefined[simp, wp]:
  "no_fail \<bottom> undefined"
  by (simp add: no_fail_def)

lemma no_fail_returnOK[simp, wp]:
  "no_fail \<top> (returnOk x)"
  by (simp add: returnOk_def)

lemma no_fail_bind[wp]:
  "\<lbrakk> no_fail P f; \<And>x. no_fail (R x) (g x); \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> no_fail (P and Q) (f >>= (\<lambda>rv. g rv))"
  apply (simp add: no_fail_def bind_def2 image_Un image_image
                   in_image_constant)
  apply (intro allI conjI impI)
   apply (fastforce simp: image_def)
  apply clarsimp
  apply (drule(1) post_by_hoare, erule in_mres)
  apply (fastforce simp: image_def)
  done

lemma no_fail_or:
  "\<lbrakk>no_fail P a; no_fail Q a\<rbrakk> \<Longrightarrow> no_fail (P or Q) a"
  by (clarsimp simp: no_fail_def)

end