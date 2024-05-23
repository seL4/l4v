(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_Prefix_Closed
  imports
    Trace_No_Trace
    Trace_Monad_Equations
    Eisbach_Tools.Rule_By_Method
begin

subsection "Prefix Closed"

text \<open>
  A monad is @{text prefix_closed} if for all traces that it returns, it also returns all incomplete traces
  leading up to it.\<close>
definition prefix_closed :: "('s, 'a) tmonad \<Rightarrow> bool" where
  "prefix_closed f = (\<forall>s. \<forall>x xs. (x # xs) \<in> fst ` f s \<longrightarrow> (xs, Incomplete) \<in> f s)"

lemmas prefix_closedD1 = prefix_closed_def[THEN iffD1, rule_format]

lemma in_fst_snd_image_eq:
  "x \<in> fst ` S = (\<exists>y. (x, y) \<in> S)"
  "y \<in> snd ` S = (\<exists>x. (x, y) \<in> S)"
  by (auto elim: image_eqI[rotated])

lemma in_fst_snd_image:
  "(x, y) \<in> S \<Longrightarrow> x \<in> fst ` S"
  "(x, y) \<in> S \<Longrightarrow> y \<in> snd ` S"
  by (auto simp: in_fst_snd_image_eq)

lemmas prefix_closedD = prefix_closedD1[OF _ in_fst_snd_image(1)]

lemma no_trace_prefix_closed:
  "no_trace f \<Longrightarrow> prefix_closed f"
  by (auto simp add: prefix_closed_def dest: no_trace_emp)


subsection \<open>Set up for @{method wp}\<close>

lemma prefix_closed_is_triple[wp_trip]:
  "prefix_closed f = triple_judgement \<top> f (\<lambda>() f. id prefix_closed f)"
  by (simp add: triple_judgement_def split: unit.split)


subsection \<open>Rules\<close>

(*
  Collect generic prefix_closed lemmas here:
   - naming convention is prefix_closed_NAME.
   - add lemmas with assumptions to [prefix_closed_cond] set
   - add lemmas without assumption to [prefix_closed_terminal] set
*)

named_theorems prefix_closed_terminal
named_theorems prefix_closed_cond

lemmas [prefix_closed_terminal] = no_trace_terminal[THEN no_trace_prefix_closed]

lemma prefix_closed_bind[wp_split]:
  "\<lbrakk>prefix_closed f; \<And>x. prefix_closed (g x)\<rbrakk> \<Longrightarrow> prefix_closed (f >>= g)"
  apply (subst prefix_closed_def, clarsimp simp: bind_def)
  apply (auto 4 4 simp: Cons_eq_append_conv split: tmres.split_asm
                 dest!: prefix_closedD[rotated] elim: rev_bexI)
  done

lemma prefix_closed_case_option[prefix_closed_cond]:
  assumes f: "prefix_closed f"
  assumes g: "\<And>x. prefix_closed (g x)"
  shows "prefix_closed (case_option f g x)"
  by (clarsimp simp: f g split: option.split)

lemma prefix_closed_alt[prefix_closed_cond]:
  "\<lbrakk> prefix_closed f; prefix_closed g \<rbrakk> \<Longrightarrow> prefix_closed (f \<sqinter> g)"
  apply (subst prefix_closed_def)
  apply (clarsimp simp add: alternative_def;
         fastforce dest: prefix_closedD)
  done

lemma prefix_closed_when[prefix_closed_cond]:
  "\<lbrakk>P \<Longrightarrow> prefix_closed f\<rbrakk> \<Longrightarrow> prefix_closed (when P f)"
  by (simp add: when_def prefix_closed_terminal)

lemma prefix_closed_unless[prefix_closed_cond]:
  "\<lbrakk>\<not>P \<Longrightarrow> prefix_closed f\<rbrakk> \<Longrightarrow> prefix_closed (unless P f)"
  by (simp add: unless_def when_def prefix_closed_terminal)

lemma prefix_closed_if[prefix_closed_cond]:
  "\<lbrakk> P \<Longrightarrow> prefix_closed f; \<not>P \<Longrightarrow> prefix_closed g \<rbrakk> \<Longrightarrow> prefix_closed (if P then f else g)"
  by simp

lemma prefix_closed_apply[prefix_closed_cond]:
  "prefix_closed (f (g x)) \<Longrightarrow> prefix_closed (f $ g x)"
  by simp

\<comment> \<open>FIXME: make proof nicer\<close>
lemma prefix_closed_liftM_eq[simp]:
  "prefix_closed (liftM f m) = prefix_closed m"
  apply (clarsimp simp: prefix_closed_def bind_def' liftM_def return_def image_def)
  apply (rule iff_allI)+
  apply safe
     apply clarsimp
     apply (drule_tac x="((a, b) # xs, map_tmres id f ba)" in bspec)
      apply clarsimp
      apply (case_tac ba; clarsimp)
      apply (auto split: tmres.splits)
  done

lemma prefix_closed_liftM[prefix_closed_cond]:
  "prefix_closed m \<Longrightarrow> prefix_closed (liftM f m)"
  by simp

lemma prefix_closed_whenE[prefix_closed_cond]:
  "\<lbrakk> G \<Longrightarrow> prefix_closed f \<rbrakk> \<Longrightarrow> prefix_closed (whenE G f)"
  by (simp add: whenE_def prefix_closed_terminal)

lemma prefix_closed_unlessE[prefix_closed_cond]:
  "\<lbrakk> \<not> G \<Longrightarrow> prefix_closed f \<rbrakk> \<Longrightarrow> prefix_closed (unlessE G f)"
  by (simp add: unlessE_def prefix_closed_terminal)

lemma prefix_closed_liftE[prefix_closed_cond]:
  "prefix_closed f \<Longrightarrow> prefix_closed (liftE f)"
  unfolding liftE_def by (wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_lift[prefix_closed_cond]:
  "\<lbrakk>\<And>y. x = Inr y \<Longrightarrow> prefix_closed (f y)\<rbrakk> \<Longrightarrow> prefix_closed (lift f x)"
  unfolding lift_def
  by (wpsimp wp: prefix_closed_terminal split: sum.splits)

lemma prefix_closed_bindE[wp_split]:
  "\<lbrakk> prefix_closed f; \<And>rv. prefix_closed (g rv)\<rbrakk> \<Longrightarrow> prefix_closed (f >>=E g)"
  unfolding bindE_def
  by (wpsimp wp: prefix_closed_cond)

lemma prefix_closed_condition[prefix_closed_cond]:
  "\<lbrakk>prefix_closed A; prefix_closed B\<rbrakk> \<Longrightarrow> prefix_closed (condition C A B)"
  unfolding condition_def prefix_closed_def
  apply clarsimp
  done

lemma prefix_closed_mapM[prefix_closed_cond]:
  "\<lbrakk>\<And>x. x \<in> set xs \<Longrightarrow> prefix_closed (f x)\<rbrakk> \<Longrightarrow> prefix_closed (mapM f xs)"
  apply (induct xs)
   apply (simp add: mapM_def sequence_def prefix_closed_terminal)
  apply (clarsimp simp: mapM_Cons)
  apply (wpsimp wp: prefix_closed_terminal)
  done

lemma prefix_closed_catch[prefix_closed_cond]:
  "\<lbrakk> prefix_closed f; \<And>x. prefix_closed (g x) \<rbrakk> \<Longrightarrow> prefix_closed (catch f g)"
  unfolding catch_def
  by (wpsimp wp: prefix_closed_terminal split: sum.split)

lemma prefix_closed_liftME[prefix_closed_cond]:
  "prefix_closed m \<Longrightarrow> prefix_closed (liftME f m)"
  unfolding liftME_def
  by (wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_handle'[prefix_closed_cond]:
  "\<lbrakk>prefix_closed f; \<And>e. prefix_closed (handler e)\<rbrakk> \<Longrightarrow> prefix_closed (f <handle2> handler)"
  unfolding handleE'_def
  by (wpsimp wp: prefix_closed_terminal split: sum.split)

lemma prefix_closed_handleE[prefix_closed_cond]:
  "\<lbrakk> prefix_closed L; \<And>r. prefix_closed (R r) \<rbrakk> \<Longrightarrow> prefix_closed (L <handle> R)"
  unfolding handleE_def
  by (simp add: prefix_closed_cond)

lemma prefix_closed_handle_elseE[prefix_closed_cond]:
  "\<lbrakk> prefix_closed f; \<And>r. prefix_closed (g r); \<And>r. prefix_closed (h r) \<rbrakk> \<Longrightarrow> prefix_closed (f <handle> g <else> h)"
  unfolding handle_elseE_def
  by (wpsimp wp: prefix_closed_terminal split: sum.split)

lemma prefix_closed_sequence[prefix_closed_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> prefix_closed m) \<Longrightarrow> prefix_closed (sequence ms)"
  unfolding sequence_def
  by (induct ms; wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_sequence_x[prefix_closed_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> prefix_closed m) \<Longrightarrow> prefix_closed (sequence_x ms)"
  unfolding sequence_x_def
  by (induct ms; wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_sequenceE[prefix_closed_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> prefix_closed m) \<Longrightarrow> prefix_closed (sequenceE ms)"
  unfolding sequenceE_def
  by (induct ms; wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_sequenceE_x[prefix_closed_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> prefix_closed m) \<Longrightarrow> prefix_closed (sequenceE_x ms)"
  unfolding sequenceE_x_def
  by (induct ms; wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_mapM_x[prefix_closed_cond]:
  "(\<And>m. m \<in> f ` set ms \<Longrightarrow> prefix_closed m) \<Longrightarrow> prefix_closed (mapM_x f ms)"
  unfolding mapM_x_def
  by (fastforce intro: prefix_closed_sequence_x)

lemma prefix_closed_mapME[prefix_closed_cond]:
  "(\<And>m. m \<in> f ` set xs \<Longrightarrow> prefix_closed m) \<Longrightarrow> prefix_closed (mapME f xs)"
  unfolding mapME_def
  by (fastforce intro: prefix_closed_sequenceE)

lemma prefix_closed_mapME_x[prefix_closed_cond]:
  "(\<And>m'. m' \<in> f ` set xs \<Longrightarrow> prefix_closed m') \<Longrightarrow> prefix_closed (mapME_x f xs)"
  unfolding mapME_x_def
  by (fastforce intro: prefix_closed_sequenceE_x)

lemma prefix_closed_filterM[prefix_closed_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> prefix_closed (P m)) \<Longrightarrow> prefix_closed (filterM P ms)"
  by (induct ms; wpsimp wp: prefix_closed_terminal split_del: if_split)

lemma prefix_closed_zipWithM_x[prefix_closed_cond]:
  "(\<And>x y. prefix_closed (f x y)) \<Longrightarrow> prefix_closed (zipWithM_x f xs ys)"
  unfolding zipWithM_x_def zipWith_def
  by (fastforce intro: prefix_closed_sequence_x)

lemma prefix_closed_zipWithM[prefix_closed_cond]:
  "(\<And>x y. prefix_closed (f x y)) \<Longrightarrow> prefix_closed (zipWithM f xs ys)"
  unfolding zipWithM_def zipWith_def
  by (fastforce intro: prefix_closed_sequence)

lemma prefix_closed_foldM[prefix_closed_cond]:
  "(\<And>x y. prefix_closed (m x y)) \<Longrightarrow> prefix_closed (foldM m xs a)"
  unfolding foldM_def
  by (induct xs; wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_foldME[prefix_closed_cond]:
  "(\<And>x y. prefix_closed (m x y)) \<Longrightarrow> prefix_closed (foldME m a xs)"
  unfolding foldME_def
  by (induct xs; wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_maybeM[prefix_closed_cond]:
  "\<forall>x. prefix_closed (f x) \<Longrightarrow> prefix_closed (maybeM f t)"
  unfolding maybeM_def
  by (fastforce intro: prefix_closed_terminal split: option.splits)

lemma prefix_closed_notM[prefix_closed_cond]:
  "prefix_closed A \<Longrightarrow> prefix_closed (notM A)"
  unfolding notM_def
  by (wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_ifM[prefix_closed_cond]:
  "\<lbrakk> prefix_closed P; prefix_closed a; prefix_closed b \<rbrakk> \<Longrightarrow> prefix_closed (ifM P a b)"
  unfolding ifM_def by wpsimp

lemma prefix_closed_ifME[prefix_closed_cond]:
  "\<lbrakk> prefix_closed P; prefix_closed a; prefix_closed b \<rbrakk> \<Longrightarrow> prefix_closed (ifME P a b)"
  unfolding ifME_def by wpsimp

lemma prefix_closed_whenM[prefix_closed_cond]:
  "\<lbrakk> prefix_closed P; prefix_closed f \<rbrakk> \<Longrightarrow> prefix_closed (whenM P f)"
  unfolding whenM_def
  by (wpsimp wp: prefix_closed_terminal prefix_closed_cond)

lemma prefix_closed_orM[prefix_closed_cond]:
  "\<lbrakk> prefix_closed A; prefix_closed B \<rbrakk> \<Longrightarrow> prefix_closed (orM A B)"
  unfolding orM_def
  by (wpsimp wp: prefix_closed_terminal prefix_closed_cond)

lemma prefix_closed_andM[prefix_closed_cond]:
  "\<lbrakk> prefix_closed A; prefix_closed B \<rbrakk> \<Longrightarrow> prefix_closed (andM A B)"
  unfolding andM_def
  by (wpsimp wp: prefix_closed_terminal prefix_closed_cond)

lemma prefix_closed_put_trace_elem[prefix_closed_terminal]:
  "prefix_closed (put_trace_elem x)"
  by (clarsimp simp: prefix_closed_def put_trace_elem_def)

lemma prefix_closed_put_trace[prefix_closed_terminal]:
  "prefix_closed (put_trace tr)"
  by (induct tr; wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_env_steps[prefix_closed_terminal]:
  "prefix_closed env_steps"
  by (wpsimp simp: env_steps_def wp: prefix_closed_terminal)

lemma prefix_closed_interference[prefix_closed_terminal]:
  "prefix_closed interference"
  by (wpsimp simp: interference_def commit_step_def wp: prefix_closed_terminal)

lemma prefix_closed_await[prefix_closed_terminal]:
  "prefix_closed (Await c)"
  by (wpsimp simp: Await_def wp: prefix_closed_terminal)

lemma prefix_closed_repeat_n[prefix_closed_cond]:
  "prefix_closed f \<Longrightarrow> prefix_closed (repeat_n n f)"
  by (induct n; wpsimp wp: prefix_closed_terminal)

lemma prefix_closed_repeat[prefix_closed_cond]:
  "prefix_closed f \<Longrightarrow> prefix_closed (repeat f)"
  apply (simp add: repeat_def)
  apply (wpsimp wp: prefix_closed_terminal prefix_closed_cond)
  done

lemma prefix_closed_parallel[wp_split]:
  "\<lbrakk>prefix_closed f; prefix_closed g\<rbrakk>
   \<Longrightarrow> prefix_closed (parallel f g)"
  apply (subst prefix_closed_def, clarsimp simp: parallel_def)
  apply (subst (asm) zip.zip_Cons)
  apply (clarsimp split: list.splits)
  apply (drule(1) prefix_closedD)+
  apply fastforce
  done

context begin
(* We want to enforce that prefix_closed_terminal only contains lemmas that have no
   assumptions. The following thm statement should fail if this is not true. *)
private lemmas check_no_assumptions_internal = iffD1[OF refl, where P="prefix_closed f" for f]
thm prefix_closed_terminal[atomized, THEN check_no_assumptions_internal]
end

(* not everything [simp] by default, because side conditions can slow down simp a lot *)
lemmas prefix_closed[wp, intro!] = prefix_closed_terminal prefix_closed_cond
lemmas [simp] = prefix_closed_terminal

end