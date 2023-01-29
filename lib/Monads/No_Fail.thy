(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas about the no_fail predicate. *)

theory No_Fail
  imports
    In_Monad
    NonDetMonadVCG
    WPSimp
begin

subsection "Non-Failure"

text \<open>
  With the failure flag, we can formulate non-failure separately from validity.
  A monad @{text m} does not fail under precondition @{text P}, if for no start
  state that satisfies the precondition it sets the failure flag.
\<close>
definition no_fail :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> bool" where
  "no_fail P m \<equiv> \<forall>s. P s \<longrightarrow> \<not>snd (m s)"


subsection \<open>@{method wpc} setup\<close>

lemma no_fail_pre[wp_pre]:
  "\<lbrakk> no_fail P f; \<And>s. Q s \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> no_fail Q f"
  by (simp add: no_fail_def)

lemma wpc_helper_no_fail_final:
  "no_fail Q f \<Longrightarrow> wpc_helper (P, P') (Q, Q') (no_fail P f)"
  by (clarsimp simp: wpc_helper_def elim!: no_fail_pre)

wpc_setup "\<lambda>m. no_fail P m" wpc_helper_no_fail_final


subsection \<open>Bundles\<close>

bundle no_pre = hoare_pre [wp_pre del] no_fail_pre [wp_pre del]

bundle classic_wp_pre =
  hoare_pre [wp_pre del]
  all_classic_wp_combs[wp_comb del]
  all_classic_wp_combs[wp_comb]


subsection \<open>Lemmas\<close>

lemma no_failD:
  "\<lbrakk> no_fail P m; P s \<rbrakk> \<Longrightarrow> \<not>(snd (m s))"
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
  by (simp add: no_fail_def select_def)

lemma no_fail_alt[wp]:
  "\<lbrakk> no_fail P f; no_fail Q g \<rbrakk> \<Longrightarrow> no_fail (P and Q) (f \<sqinter> g)"
  by (simp add: no_fail_def alternative_def)

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
  "\<lbrakk> no_fail P f; \<And>rv. no_fail (R rv) (g rv); \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> no_fail (P and Q) (f >>= (\<lambda>rv. g rv))"
  unfolding no_fail_def bind_def
  using post_by_hoare by fastforce

lemma no_fail_assume_pre:
  "(\<And>s. P s \<Longrightarrow> no_fail P f) \<Longrightarrow> no_fail P f"
  by (simp add: no_fail_def)

lemma no_fail_liftM_eq[simp]:
  "no_fail P (liftM f m) = no_fail P m"
  by (auto simp: liftM_def no_fail_def bind_def return_def)

lemma no_fail_select_f[wp]:
  "no_fail (\<lambda>s. \<not>snd S) (select_f S)"
  by (simp add: select_f_def no_fail_def)

lemma no_fail_liftM[wp]:
  "no_fail P m \<Longrightarrow> no_fail P (liftM f m)"
  by simp

lemma no_fail_pre_and:
  "no_fail P f \<Longrightarrow> no_fail (P and Q) f"
  by (erule no_fail_pre) simp

lemma no_fail_spec:
  "\<lbrakk> \<And>s. no_fail (((=) s) and P) f \<rbrakk> \<Longrightarrow> no_fail P f"
  by (simp add: no_fail_def)

lemma no_fail_assertE[wp]:
  "no_fail (\<lambda>_. P) (assertE P)"
  by (simp add: assertE_def split: if_split)

lemma no_fail_spec_pre:
  "\<lbrakk> no_fail (((=) s) and P') f; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> no_fail (((=) s) and P) f"
  by (erule no_fail_pre, simp)

lemma no_fail_whenE[wp]:
  "\<lbrakk> G \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. G \<longrightarrow> P s) (whenE G f)"
  by (simp add: whenE_def split: if_split)

lemma no_fail_unlessE[wp]:
  "\<lbrakk> \<not> G \<Longrightarrow> no_fail P f \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. \<not> G \<longrightarrow> P s) (unlessE G f)"
  by (simp add: unlessE_def split: if_split)

lemma no_fail_throwError[wp]:
  "no_fail \<top> (throwError e)"
  by (simp add: throwError_def)

lemma no_fail_liftE[wp]:
  "no_fail P f \<Longrightarrow> no_fail P (liftE f)"
  unfolding liftE_def by wpsimp

lemma no_fail_gets_the[wp]:
  "no_fail (\<lambda>s. f s \<noteq> None) (gets_the f)"
  unfolding gets_the_def
  by wpsimp

lemma no_fail_lift:
  "(\<And>y. x = Inr y \<Longrightarrow> no_fail P (f y)) \<Longrightarrow> no_fail (\<lambda>s. \<not>isl x \<longrightarrow> P s) (lift f x)"
  unfolding lift_def
  by (wpsimp wp: no_fail_throwError split: sum.splits | assumption)+

lemma validE_R_valid_eq:
  "\<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>, - = \<lbrace>Q\<rbrace> f \<lbrace>\<lambda>rv s. \<not> isl rv \<longrightarrow> R (projr rv) s\<rbrace>"
  unfolding validE_R_def validE_def valid_def
  by (fastforce split: sum.splits prod.split)

lemma no_fail_bindE[wp]:
  "\<lbrakk> no_fail P f; \<And>rv. no_fail (R rv) (g rv); \<lbrace>Q\<rbrace> f \<lbrace>R\<rbrace>,- \<rbrakk>
     \<Longrightarrow> no_fail (P and Q) (f >>=E g)"
  unfolding bindE_def
  by (wpsimp wp: no_fail_lift simp: validE_R_valid_eq | assumption)+

lemma no_fail_False[simp]:
  "no_fail (\<lambda>_. False) X"
  by (clarsimp simp: no_fail_def)

lemma no_fail_gets_map[wp]:
  "no_fail (\<lambda>s. f s p \<noteq> None) (gets_map f p)"
  unfolding gets_map_def by wpsimp

lemma no_fail_or:
  "\<lbrakk>no_fail P a; no_fail Q a\<rbrakk> \<Longrightarrow> no_fail (P or Q) a"
  by (clarsimp simp: no_fail_def)

lemma no_fail_state_assert[wp]:
  "no_fail P (state_assert P)"
  unfolding state_assert_def
  by wpsimp

lemma no_fail_condition:
  "\<lbrakk>no_fail Q A; no_fail R B\<rbrakk> \<Longrightarrow> no_fail (\<lambda>s. (C s \<longrightarrow> Q s) \<and> (\<not> C s \<longrightarrow> R s)) (condition C A B)"
  unfolding condition_def no_fail_def
  by clarsimp

end
