(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Empty_Fail
  imports
    NonDetMonad
    WPSimp
begin

section \<open>Monads that are wellformed w.r.t. failure\<close>

text \<open>
  Usually, well-formed monads constructed from the primitives in NonDetMonad will have the following
  property: if they return an empty set of results, they will have the failure flag set.\<close>
definition empty_fail :: "('s,'a) nondet_monad \<Rightarrow> bool" where
  "empty_fail m \<equiv> \<forall>s. fst (m s) = {} \<longrightarrow> snd (m s)"

text \<open>Useful in forcing otherwise unknown executions to have the @{const empty_fail} property.\<close>
definition mk_ef :: "'a set \<times> bool \<Rightarrow> 'a set \<times> bool" where
  "mk_ef S \<equiv> (fst S, fst S = {} \<or> snd S)"


subsection \<open>WPC setup\<close>

lemma wpc_helper_empty_fail_final:
  "empty_fail f \<Longrightarrow> wpc_helper (P, P') (Q, Q') (empty_fail f)"
  by (clarsimp simp: wpc_helper_def)

wpc_setup "\<lambda>m. empty_fail m" wpc_helper_empty_fail_final


subsection \<open>@{const empty_fail} intro/dest rules\<close>

lemma empty_failI:
  "(\<And>s. fst (m s) = {} \<Longrightarrow> snd (m s)) \<Longrightarrow> empty_fail m"
  by (simp add: empty_fail_def)

lemma empty_failD:
  "\<lbrakk> empty_fail m; fst (m s) = {} \<rbrakk> \<Longrightarrow> snd (m s)"
  by (simp add: empty_fail_def)

lemma empty_fail_not_snd:
  "\<lbrakk> \<not> snd (m s); empty_fail m \<rbrakk> \<Longrightarrow> \<exists>v. v \<in> fst (m s)"
  by (fastforce simp: empty_fail_def)

lemmas empty_failD2 = empty_fail_not_snd[rotated]

lemma empty_failD3:
  "\<lbrakk> empty_fail f; \<not> snd (f s) \<rbrakk> \<Longrightarrow> fst (f s) \<noteq> {}"
  by (drule(1) empty_failD2, clarsimp)

lemma empty_fail_bindD1:
  "empty_fail (a >>= b) \<Longrightarrow> empty_fail a"
  unfolding empty_fail_def bind_def
  by (fastforce simp: split_def image_image)


subsection \<open>Wellformed monads\<close>

(*
  Collect generic empty_fail lemmas here:
   - naming convention is emtpy_fail_NAME.
   - add all new lemmas to [empty_fail] set, unless they have side conditions
     that are not [empty_fail]
*)

named_theorems empty_fail

lemma empty_fail_modify[empty_fail]:
  "empty_fail (modify f)"
  by (simp add: empty_fail_def simpler_modify_def)

lemma empty_fail_gets[empty_fail]:
  "empty_fail (gets f)"
  by (simp add: empty_fail_def simpler_gets_def)

(* Not in empty_fail set, because it has a non-[empty_fail] side condition *)
lemma empty_fail_select_f:
  assumes ef: "fst S = {} \<Longrightarrow> snd S"
  shows "empty_fail (select_f S)"
  by (fastforce simp add: empty_fail_def select_f_def intro: ef)

lemma empty_fail_bind[empty_fail]:
  "\<lbrakk> empty_fail a; \<And>x. empty_fail (b x) \<rbrakk> \<Longrightarrow> empty_fail (a >>= b)"
  by (fastforce simp: bind_def empty_fail_def split_def)

lemma empty_fail_return[empty_fail]:
  "empty_fail (return x)"
  by (simp add: empty_fail_def return_def)

lemma empty_fail_error_bits[empty_fail]:
  "empty_fail (returnOk v)"
  "empty_fail (throwError v)"
  "empty_fail (liftE f) = empty_fail f"
  by (fastforce simp: returnOk_def throwError_def liftE_def empty_fail_def bind_def return_def)+

lemma empty_fail_lift[empty_fail]:
  "\<lbrakk> \<And>x. empty_fail (f x) \<rbrakk> \<Longrightarrow> empty_fail (lift f x)"
  unfolding lift_def
  by (auto simp: empty_fail split: sum.split)

lemma empty_fail_bindE[empty_fail]:
  "\<lbrakk> empty_fail f; \<And>rv. empty_fail (g rv) \<rbrakk> \<Longrightarrow> empty_fail (f >>=E g)"
  by (simp add: bindE_def empty_fail)

lemma empty_fail_If[empty_fail]:
  "\<lbrakk> empty_fail f; empty_fail g \<rbrakk> \<Longrightarrow> empty_fail (if P then f else g)"
  by (simp split: if_split)

lemma empty_fail_mapM[empty_fail]:
  assumes m: "\<And>x. empty_fail (m x)"
  shows "empty_fail (mapM m xs)"
proof (induct xs)
  case Nil
  thus ?case by (simp add: mapM_def sequence_def empty_fail)
next
  case Cons
  have P: "\<And>m x xs. mapM m (x # xs) = (do y \<leftarrow> m x; ys \<leftarrow> (mapM m xs); return (y # ys) od)"
    by (simp add: mapM_def sequence_def Let_def)
  from Cons
  show ?case by (simp add: P m empty_fail)
qed

lemma empty_fail_fail[empty_fail]:
  "empty_fail fail"
  by (simp add: fail_def empty_fail_def)

lemma empty_fail_assert[empty_fail]:
  "empty_fail (assert P)"
  unfolding assert_def by (simp add: empty_fail)

lemma empty_fail_assert_opt[empty_fail]:
  "empty_fail (assert_opt x)"
  by (simp add: assert_opt_def empty_fail split: option.splits)

lemma empty_fail_mk_ef[empty_fail]:
  "empty_fail (mk_ef o m)"
  by (simp add: empty_fail_def mk_ef_def)

lemma empty_fail_gets_map[empty_fail]:
  "empty_fail (gets_map f p)"
  unfolding gets_map_def by (simp add: empty_fail)

lemma empty_fail_whenEs[empty_fail]:
  "empty_fail f \<Longrightarrow> empty_fail (whenE P f)"
  "empty_fail f \<Longrightarrow> empty_fail (unlessE P f)"
  by (auto simp add: whenE_def unlessE_def empty_fail)

lemma empty_fail_assertE[empty_fail]:
  "empty_fail (assertE P)"
  by (simp add: assertE_def empty_fail split: if_split)

lemma empty_fail_get[empty_fail]:
  "empty_fail get"
  by (simp add: empty_fail_def get_def)

lemma empty_fail_catch[empty_fail]:
  "\<lbrakk> empty_fail f; \<And>x. empty_fail (g x) \<rbrakk> \<Longrightarrow> empty_fail (catch f g)"
  by (simp add: catch_def empty_fail split: sum.split)

lemma empty_fail_select[empty_fail]:
  "empty_fail (select V) = (V \<noteq> {})"
  by (clarsimp simp: select_def empty_fail_def)

lemma empty_fail_guard[empty_fail]:
  "empty_fail (state_assert G)"
  by (clarsimp simp: state_assert_def empty_fail)

lemma empty_fail_spec[empty_fail]:
  "empty_fail (state_select F)"
  by (clarsimp simp: state_select_def empty_fail_def)

lemma empty_fail_when[empty_fail]:
  "empty_fail x \<Longrightarrow> empty_fail (when P x)"
  unfolding when_def by (simp add: empty_fail)

lemma empty_fail_unless[empty_fail]:
  "empty_fail f \<Longrightarrow> empty_fail (unless P f)"
  by (simp add: unless_def empty_fail)

lemma empty_fail_liftM[empty_fail]:
  "empty_fail (liftM f m) = empty_fail m"
  unfolding liftM_def
  by (fastforce dest: empty_fail_bindD1 simp: empty_fail)

lemma empty_fail_handleE[empty_fail]:
  "\<lbrakk> empty_fail L; \<And>r. empty_fail (R r) \<rbrakk> \<Longrightarrow> empty_fail (L <handle> R)"
  by (clarsimp simp: handleE_def handleE'_def empty_fail split: sum.splits)


declare empty_fail[simp, intro!, wp]

end
