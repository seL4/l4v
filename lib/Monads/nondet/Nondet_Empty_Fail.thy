(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Nondet_Empty_Fail
  imports
    Nondet_Monad
    WPSimp
begin

section \<open>Monads that are wellformed w.r.t. failure\<close>

text \<open>
  Usually, well-formed monads constructed from the primitives in Nondet_Monad will have the following
  property: if they return an empty set of results, they will have the failure flag set.\<close>
definition empty_fail :: "('s,'a) nondet_monad \<Rightarrow> bool" where
  "empty_fail m \<equiv> \<forall>s. fst (m s) = {} \<longrightarrow> snd (m s)"

text \<open>Useful in forcing otherwise unknown executions to have the @{const empty_fail} property.\<close>
definition mk_ef :: "'a set \<times> bool \<Rightarrow> 'a set \<times> bool" where
  "mk_ef S \<equiv> (fst S, fst S = {} \<or> snd S)"


subsection \<open>WPC setup\<close>

lemma wpc_helper_empty_fail_final:
  "empty_fail f \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') (empty_fail f)"
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
   - add lemmas with assumptions to [empty_fail_cond] set
   - add lemmas without assumption to [empty_fail_term] set
*)

named_theorems empty_fail_term
named_theorems empty_fail_cond

lemma empty_fail_K_bind[empty_fail_cond]:
  "empty_fail f \<Longrightarrow> empty_fail (K_bind f x)"
  by simp

lemma empty_fail_fun_app[empty_fail_cond]:
  "empty_fail (f x) \<Longrightarrow> empty_fail (f $ x)"
  by simp

(* empty_fail as such does not need context, but empty_fail_select_f does, so we need to build
   up context in other rules *)
lemma empty_fail_If[empty_fail_cond]:
  "\<lbrakk> P \<Longrightarrow> empty_fail f; \<not>P \<Longrightarrow> empty_fail g \<rbrakk> \<Longrightarrow> empty_fail (if P then f else g)"
  by (simp split: if_split)

lemma empty_fail_If_applied[empty_fail_cond]:
  "\<lbrakk> P \<Longrightarrow> empty_fail (f x); \<not>P \<Longrightarrow> empty_fail (g x) \<rbrakk> \<Longrightarrow> empty_fail ((if P then f else g) x)"
  by simp

lemma empty_fail_put[empty_fail_term]:
  "empty_fail (put f)"
  by (simp add: put_def empty_fail_def)

lemma empty_fail_modify[empty_fail_term]:
  "empty_fail (modify f)"
  by (simp add: empty_fail_def simpler_modify_def)

lemma empty_fail_gets[empty_fail_term]:
  "empty_fail (gets f)"
  by (simp add: empty_fail_def simpler_gets_def)

lemma empty_fail_select[empty_fail_cond]:
  "S \<noteq> {} \<Longrightarrow> empty_fail (select S)"
  by (simp add: empty_fail_def select_def)

lemma empty_fail_select_f[empty_fail_cond]:
  assumes ef: "fst S = {} \<Longrightarrow> snd S"
  shows "empty_fail (select_f S)"
  by (fastforce simp add: empty_fail_def select_f_def intro: ef)

lemma empty_fail_bind[empty_fail_cond]:
  "\<lbrakk> empty_fail a; \<And>x. empty_fail (b x) \<rbrakk> \<Longrightarrow> empty_fail (a >>= b)"
  by (fastforce simp: bind_def empty_fail_def split_def)

lemma empty_fail_return[empty_fail_term]:
  "empty_fail (return x)"
  by (simp add: empty_fail_def return_def)

lemma empty_fail_returnOk[empty_fail_term]:
  "empty_fail (returnOk v)"
  by (fastforce simp: returnOk_def empty_fail_term)

lemma empty_fail_throwError[empty_fail_term]:
  "empty_fail (throwError v)"
  by (fastforce simp: throwError_def empty_fail_term)

lemma empty_fail_lift[empty_fail_cond]:
  "\<lbrakk> \<And>x. empty_fail (f x) \<rbrakk> \<Longrightarrow> empty_fail (lift f x)"
  unfolding lift_def
  by (auto simp: empty_fail_term split: sum.split)

lemma empty_fail_liftE[empty_fail_cond]:
  "empty_fail f \<Longrightarrow> empty_fail (liftE f)"
  by (simp add: liftE_def empty_fail_cond empty_fail_term)

lemma empty_fail_bindE[empty_fail_cond]:
  "\<lbrakk> empty_fail f; \<And>rv. empty_fail (g rv) \<rbrakk> \<Longrightarrow> empty_fail (f >>=E g)"
  by (simp add: bindE_def empty_fail_cond)

lemma empty_fail_mapM[empty_fail_cond]:
  assumes m: "\<And>x. x \<in> set xs \<Longrightarrow> empty_fail (m x)"
  shows "empty_fail (mapM m xs)"
using m
proof (induct xs)
  case Nil
  thus ?case by (simp add: mapM_def sequence_def empty_fail_term)
next
  case Cons
  have P: "\<And>m x xs. mapM m (x # xs) = (do y \<leftarrow> m x; ys \<leftarrow> (mapM m xs); return (y # ys) od)"
    by (simp add: mapM_def sequence_def Let_def)
  from Cons
  show ?case by (simp add: P m empty_fail_cond empty_fail_term)
qed

lemma empty_fail_fail[empty_fail_term]:
  "empty_fail fail"
  by (simp add: fail_def empty_fail_def)

lemma empty_fail_assert[empty_fail_term]:
  "empty_fail (assert P)"
  unfolding assert_def by (simp add: empty_fail_term)

lemma empty_fail_assert_opt[empty_fail_term]:
  "empty_fail (assert_opt x)"
  by (simp add: assert_opt_def empty_fail_term split: option.splits)

lemma empty_fail_mk_ef[empty_fail_term]:
  "empty_fail (mk_ef o m)"
  by (simp add: empty_fail_def mk_ef_def)

lemma empty_fail_gets_the[empty_fail_term]:
  "empty_fail (gets_the f)"
  unfolding gets_the_def
  by (simp add: empty_fail_cond empty_fail_term)

lemma empty_fail_gets_map[empty_fail_term]:
  "empty_fail (gets_map f p)"
  unfolding gets_map_def
  by (simp add: empty_fail_term empty_fail_cond)

lemma empty_fail_whenEs[empty_fail_cond]:
  "(P \<Longrightarrow> empty_fail f) \<Longrightarrow> empty_fail (whenE P f)"
  "(\<not>P \<Longrightarrow> empty_fail f) \<Longrightarrow> empty_fail (unlessE P f)"
  by (auto simp add: whenE_def unlessE_def empty_fail_term)

lemma empty_fail_assertE[empty_fail_term]:
  "empty_fail (assertE P)"
  by (simp add: assertE_def empty_fail_term)

lemma empty_fail_get[empty_fail_term]:
  "empty_fail get"
  by (simp add: empty_fail_def get_def)

lemma empty_fail_catch[empty_fail_cond]:
  "\<lbrakk> empty_fail f; \<And>x. empty_fail (g x) \<rbrakk> \<Longrightarrow> empty_fail (catch f g)"
  by (simp add: catch_def empty_fail_cond empty_fail_term split: sum.split)

lemma empty_fail_guard[empty_fail_term]:
  "empty_fail (state_assert G)"
  by (clarsimp simp: state_assert_def empty_fail_cond empty_fail_term)

lemma empty_fail_spec[empty_fail_term]:
  "empty_fail (state_select F)"
  by (clarsimp simp: state_select_def empty_fail_def)

lemma empty_fail_when[empty_fail_cond]:
  "(P \<Longrightarrow> empty_fail x) \<Longrightarrow> empty_fail (when P x)"
  unfolding when_def
  by (simp add: empty_fail_term)

lemma empty_fail_unless[empty_fail_cond]:
  "(\<not>P \<Longrightarrow> empty_fail f) \<Longrightarrow> empty_fail (unless P f)"
  unfolding unless_def
  by (simp add: empty_fail_cond)

lemma empty_fail_liftM[empty_fail_cond]:
  "empty_fail m \<Longrightarrow> empty_fail (liftM f m)"
  unfolding liftM_def
  by (fastforce simp: empty_fail_term empty_fail_cond)

lemma empty_fail_liftME[empty_fail_cond]:
  "empty_fail m \<Longrightarrow> empty_fail (liftME f m)"
  unfolding liftME_def
  by (simp add: empty_fail_term empty_fail_cond)

lemma empty_fail_handleE[empty_fail_cond]:
  "\<lbrakk> empty_fail L; \<And>r. empty_fail (R r) \<rbrakk> \<Longrightarrow> empty_fail (L <handle> R)"
  by (clarsimp simp: handleE_def handleE'_def empty_fail_term empty_fail_cond split: sum.splits)

lemma empty_fail_handle'[empty_fail_cond]:
  "\<lbrakk>empty_fail f; \<And>e. empty_fail (handler e)\<rbrakk> \<Longrightarrow> empty_fail (f <handle2> handler)"
  unfolding handleE'_def
  by (fastforce simp: empty_fail_term empty_fail_cond split: sum.splits)

lemma empty_fail_sequence[empty_fail_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (sequence ms)"
  unfolding sequence_def
  by (induct ms; simp add: empty_fail_term empty_fail_cond)

lemma empty_fail_sequence_x[empty_fail_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (sequence_x ms)"
  unfolding sequence_x_def
  by (induct ms; simp add: empty_fail_term empty_fail_cond)

lemma empty_fail_sequenceE[empty_fail_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (sequenceE ms)"
  unfolding sequenceE_def
  by (induct ms; simp add: empty_fail_term empty_fail_cond)

lemma empty_fail_sequenceE_x[empty_fail_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (sequenceE_x ms)"
  unfolding sequenceE_x_def
  by (induct ms; simp add: empty_fail_term empty_fail_cond)

lemma empty_fail_mapM_x[empty_fail_cond]:
  "(\<And>m. m \<in> f ` set ms \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (mapM_x f ms)"
  unfolding mapM_x_def
  by (fastforce intro: empty_fail_term empty_fail_cond)

lemma empty_fail_mapME[empty_fail_cond]:
  "(\<And>m. m \<in> f ` set xs \<Longrightarrow> empty_fail m) \<Longrightarrow> empty_fail (mapME f xs)"
  unfolding mapME_def
  by (fastforce intro: empty_fail_term empty_fail_cond)

lemma empty_fail_mapME_x[empty_fail_cond]:
  "(\<And>m'. m' \<in> f ` set xs \<Longrightarrow> empty_fail m') \<Longrightarrow> empty_fail (mapME_x f xs)"
  unfolding mapME_x_def
  by (fastforce intro: empty_fail_term empty_fail_cond)

lemma empty_fail_filterM[empty_fail_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> empty_fail (P m)) \<Longrightarrow> empty_fail (filterM P ms)"
  by (induct ms; simp add: empty_fail_term empty_fail_cond)

lemma empty_fail_zipWithM_x[empty_fail_cond]:
  "(\<And>x y. empty_fail (f x y)) \<Longrightarrow> empty_fail (zipWithM_x f xs ys)"
  unfolding zipWithM_x_def zipWith_def
  by (fastforce intro: empty_fail_term empty_fail_cond)

lemma empty_fail_zipWithM[empty_fail_cond]:
  "(\<And>x y. empty_fail (f x y)) \<Longrightarrow> empty_fail (zipWithM f xs ys)"
  unfolding zipWithM_def zipWith_def
  by (fastforce intro: empty_fail_term empty_fail_cond)

lemma empty_fail_maybeM[empty_fail_cond]:
  "\<forall>x. empty_fail (f x) \<Longrightarrow> empty_fail (maybeM f t)"
  unfolding maybeM_def
  by (fastforce intro: empty_fail_term split: option.splits)

lemma empty_fail_ifM[empty_fail_cond]:
  "\<lbrakk> empty_fail P; empty_fail a; empty_fail b \<rbrakk> \<Longrightarrow> empty_fail (ifM P a b)"
  by (simp add: ifM_def empty_fail_cond)

lemma empty_fail_ifME[empty_fail_cond]:
  "\<lbrakk> empty_fail P; empty_fail a; empty_fail b \<rbrakk> \<Longrightarrow> empty_fail (ifME P a b)"
  by (simp add: ifME_def empty_fail_cond)

lemma empty_fail_whenM[empty_fail_cond]:
  "\<lbrakk> empty_fail P; empty_fail f \<rbrakk> \<Longrightarrow> empty_fail (whenM P f)"
  by (simp add: whenM_def empty_fail_term empty_fail_cond)

lemma empty_fail_andM[empty_fail_cond]:
  "\<lbrakk> empty_fail A; empty_fail B \<rbrakk> \<Longrightarrow> empty_fail (andM A B)"
  by (simp add: andM_def empty_fail_term empty_fail_cond)

lemma empty_fail_orM[empty_fail_cond]:
  "\<lbrakk> empty_fail A; empty_fail B \<rbrakk> \<Longrightarrow> empty_fail (orM A B)"
  by (simp add: orM_def empty_fail_term empty_fail_cond)

lemma empty_fail_notM[empty_fail_cond]:
  "empty_fail A \<Longrightarrow> empty_fail (notM A)"
  by (simp add: notM_def empty_fail_term empty_fail_cond)

(* not everything [simp] by default, because side conditions can slow down simp a lot *)
lemmas empty_fail[wp, intro!] = empty_fail_term empty_fail_cond
lemmas [simp] = empty_fail_term


subsection \<open>Equations and legacy names\<close>

lemma empty_fail_select_eq[simp]:
  "empty_fail (select V) = (V \<noteq> {})"
  by (clarsimp simp: select_def empty_fail_def)

lemma empty_fail_liftM_eq[simp]:
  "empty_fail (liftM f m) = empty_fail m"
  unfolding liftM_def
  by (fastforce dest: empty_fail_bindD1)

lemma empty_fail_liftE_eq[simp]:
  "empty_fail (liftE f) = empty_fail f"
  by (fastforce simp: liftE_def empty_fail_def bind_def)

lemma liftME_empty_fail_eq[simp]:
  "empty_fail (liftME f m) = empty_fail m"
  unfolding liftME_def
  by (fastforce dest: empty_fail_bindD1 simp: bindE_def)

(* legacy name binding *)
lemmas empty_fail_error_bits = empty_fail_returnOk empty_fail_throwError empty_fail_liftE_eq

end
