(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Trace_No_Trace
  imports
    Trace_Monad
    WPSimp
begin

subsection "No Trace"

text \<open>
  A monad of type @{text tmonad} does not have a trace iff for all starting
  states, all of the potential outcomes have the empty list as a trace and do
  not return an @{term Incomplete} result.\<close>
definition no_trace :: "('s,'a) tmonad  \<Rightarrow> bool" where
  "no_trace f = (\<forall>tr res s. (tr, res) \<in> f s \<longrightarrow> tr = [] \<and> res \<noteq> Incomplete)"

lemmas no_traceD = no_trace_def[THEN iffD1, rule_format]

lemma no_trace_emp:
  "\<lbrakk>no_trace f; (tr, r) \<in> f s\<rbrakk> \<Longrightarrow> tr = []"
  by (simp add: no_traceD)

lemma no_trace_Incomplete_mem:
  "no_trace f \<Longrightarrow> (tr, Incomplete) \<notin> f s"
  by (auto dest: no_traceD)

lemma no_trace_Incomplete_eq:
  "\<lbrakk>no_trace f; (tr, res) \<in> f s\<rbrakk> \<Longrightarrow> res \<noteq> Incomplete"
  by (auto dest: no_traceD)


subsection \<open>Set up for @{method wp}\<close>

lemma no_trace_is_triple[wp_trip]:
  "no_trace f = triple_judgement \<top> f (\<lambda>() f. id no_trace f)"
  by (simp add: triple_judgement_def split: unit.split)


subsection \<open>Rules\<close>

(*
  Collect generic no_trace lemmas here:
   - naming convention is no_trace_NAME.
   - add lemmas with assumptions to [no_trace_cond] set
   - add lemmas without assumption to [no_trace_terminal] set
*)

named_theorems no_trace_cond
named_theorems no_trace_terminal

lemma no_trace_bind[wp_split]:
  "\<lbrakk>no_trace f; \<forall>rv. no_trace (g rv)\<rbrakk>
   \<Longrightarrow> no_trace (do rv \<leftarrow> f; g rv od)"
  apply (subst no_trace_def)
  apply (clarsimp simp: bind_def split: tmres.split_asm;
         fastforce dest: no_traceD)
  done

lemma no_trace_get[no_trace_terminal]:
  "no_trace get"
  by (simp add: no_trace_def get_def)

lemma no_trace_put[no_trace_terminal]:
  "no_trace (put s)"
  by (simp add: no_trace_def put_def)

lemma no_trace_modify[no_trace_terminal]:
  "no_trace (modify f)"
  by (wpsimp simp: modify_def wp: no_trace_terminal)

lemma no_trace_return[no_trace_terminal]:
  "no_trace (return v)"
  by (simp add: no_trace_def return_def)

lemma no_trace_fail[no_trace_terminal]:
  "no_trace fail"
  by (simp add: no_trace_def fail_def)

lemma no_trace_returnOk[no_trace_terminal]:
  "no_trace (returnOk v)"
  by (simp add: returnOk_def no_trace_terminal)

lemma no_trace_select[no_trace_terminal]:
  "no_trace (select S)"
  by (clarsimp simp add: no_trace_def select_def)

lemma no_trace_gets[no_trace_terminal]:
  "no_trace (gets f)"
  by (wpsimp simp: gets_def wp: no_trace_terminal)

lemma no_trace_assert[no_trace_terminal]:
  "no_trace (assert P)"
  by (simp add: assert_def no_trace_terminal)

lemma no_trace_case_option[no_trace_cond]:
  assumes f: "no_trace f"
  assumes g: "\<And>x. no_trace (g x)"
  shows "no_trace (case_option f g x)"
  by (clarsimp simp: f g split: option.split)

lemma no_trace_assert_opt[no_trace_terminal]:
  "no_trace (assert_opt Q)"
  by (simp add: assert_opt_def no_trace_terminal no_trace_cond)

lemma no_trace_alt[no_trace_cond]:
  "\<lbrakk> no_trace f; no_trace g \<rbrakk> \<Longrightarrow> no_trace (f \<sqinter> g)"
  apply (subst no_trace_def)
  apply (clarsimp simp add: alternative_def;
         fastforce dest: no_traceD)
  done

lemma no_trace_when[no_trace_cond]:
  "\<lbrakk>P \<Longrightarrow> no_trace f\<rbrakk> \<Longrightarrow> no_trace (when P f)"
  by (simp add: when_def no_trace_terminal)

lemma no_trace_unless[no_trace_cond]:
  "\<lbrakk>\<not>P \<Longrightarrow> no_trace f\<rbrakk> \<Longrightarrow> no_trace (unless P f)"
  by (simp add: unless_def when_def no_trace_terminal)

lemma no_trace_if[no_trace_cond]:
  "\<lbrakk> P \<Longrightarrow> no_trace f; \<not>P \<Longrightarrow> no_trace g \<rbrakk> \<Longrightarrow> no_trace (if P then f else g)"
  by simp

lemma no_trace_apply[no_trace_cond]:
  "no_trace (f (g x)) \<Longrightarrow> no_trace (f $ g x)"
  by simp

\<comment> \<open>FIXME: make proof nicer\<close>
lemma no_trace_liftM_eq[simp]:
  "no_trace (liftM f m) = no_trace m"
  apply (clarsimp simp: no_trace_def bind_def liftM_def return_def)
  apply safe
     apply (drule_tac x=tr in spec)
     apply (drule_tac x="map_tmres id f res" in spec)
     apply (drule mp)
      apply (rule exI)
      apply (erule rev_bexI)
      apply (clarsimp split: tmres.splits)
     apply clarsimp
    apply (drule spec, drule spec, drule mp, rule exI, erule rev_bexI)
     apply (auto split: tmres.splits)
  done

lemma no_trace_liftM[no_trace_cond]:
  "no_trace m \<Longrightarrow> no_trace (liftM f m)"
  by simp

lemma no_trace_assertE[no_trace_terminal]:
  "no_trace (assertE P)"
  by (simp add: assertE_def no_trace_terminal)

lemma no_trace_whenE[no_trace_cond]:
  "\<lbrakk> G \<Longrightarrow> no_trace f \<rbrakk> \<Longrightarrow> no_trace (whenE G f)"
  by (simp add: whenE_def no_trace_terminal)

lemma no_trace_unlessE[no_trace_cond]:
  "\<lbrakk> \<not> G \<Longrightarrow> no_trace f \<rbrakk> \<Longrightarrow> no_trace (unlessE G f)"
  by (simp add: unlessE_def no_trace_terminal)

lemma no_trace_throwError[no_trace_terminal]:
  "no_trace (throwError e)"
  by (simp add: throwError_def no_trace_terminal)

lemma no_trace_throw_opt[no_trace_terminal]:
  "no_trace (throw_opt ex x)"
  unfolding throw_opt_def
  by (simp add: no_trace_terminal no_trace_cond)

lemma no_trace_liftE[no_trace_cond]:
  "no_trace f \<Longrightarrow> no_trace (liftE f)"
  unfolding liftE_def by (wpsimp wp: no_trace_terminal)

lemma no_trace_gets_the[no_trace_terminal]:
  "no_trace (gets_the f)"
  unfolding gets_the_def
  by (wpsimp wp: no_trace_terminal)

lemma no_trace_lift[no_trace_cond]:
  "\<lbrakk>\<And>y. x = Inr y \<Longrightarrow> no_trace (f y)\<rbrakk> \<Longrightarrow> no_trace (lift f x)"
  unfolding lift_def
  by (wpsimp wp: no_trace_terminal split: sum.splits)

lemma no_trace_bindE[wp_split]:
  "\<lbrakk> no_trace f; \<And>rv. no_trace (g rv)\<rbrakk> \<Longrightarrow> no_trace (f >>=E g)"
  unfolding bindE_def
  by (wpsimp wp: no_trace_cond)

lemma no_trace_gets_map[no_trace_terminal]:
  "no_trace (gets_map f p)"
  unfolding gets_map_def by (wpsimp wp: no_trace_terminal)

lemma no_trace_state_assert[no_trace_terminal]:
  "no_trace (state_assert P)"
  unfolding state_assert_def
  by (wpsimp wp: no_trace_terminal)

lemma no_trace_condition[no_trace_cond]:
  "\<lbrakk>no_trace A; no_trace B\<rbrakk> \<Longrightarrow> no_trace (condition C A B)"
  unfolding condition_def no_trace_def
  apply clarsimp
  apply fastforce
  done

lemma no_trace_mapM[no_trace_cond]:
  assumes m: "\<And>x. x \<in> set xs \<Longrightarrow> no_trace (m x)"
  shows "no_trace (mapM m xs)"
  using m
proof (induct xs)
  case Nil
  thus ?case by (simp add: mapM_def sequence_def no_trace_terminal)
next
  case Cons
  have P: "\<And>m x xs. mapM m (x # xs) = (do y \<leftarrow> m x; ys \<leftarrow> (mapM m xs); return (y # ys) od)"
    by (simp add: mapM_def sequence_def Let_def)
  from Cons
  show ?case
    apply (simp add: P)
    apply (wpsimp wp: no_trace_terminal)
    done
qed

lemma no_trace_catch[no_trace_cond]:
  "\<lbrakk> no_trace f; \<And>x. no_trace (g x) \<rbrakk> \<Longrightarrow> no_trace (catch f g)"
  unfolding catch_def
  by (wpsimp wp: no_trace_terminal split: sum.split)

lemma no_trace_state_select[no_trace_terminal]:
  "no_trace (state_select F)"
  unfolding state_select_def2
  by (wpsimp wp: no_trace_terminal)

lemma no_trace_liftME[no_trace_cond]:
  "no_trace m \<Longrightarrow> no_trace (liftME f m)"
  unfolding liftME_def
  by (wpsimp wp: no_trace_terminal)

lemma no_trace_handle'[no_trace_cond]:
  "\<lbrakk>no_trace f; \<And>e. no_trace (handler e)\<rbrakk> \<Longrightarrow> no_trace (f <handle2> handler)"
  unfolding handleE'_def
  by (wpsimp wp: no_trace_terminal split: sum.split)

lemma no_trace_handleE[no_trace_cond]:
  "\<lbrakk> no_trace L; \<And>r. no_trace (R r) \<rbrakk> \<Longrightarrow> no_trace (L <handle> R)"
  unfolding handleE_def
  by (simp add: no_trace_cond)

lemma no_trace_handle_elseE[no_trace_cond]:
  "\<lbrakk> no_trace f; \<And>r. no_trace (g r); \<And>r. no_trace (h r) \<rbrakk> \<Longrightarrow> no_trace (f <handle> g <else> h)"
  unfolding handle_elseE_def
  by (wpsimp wp: no_trace_terminal split: sum.split)

lemma no_trace_sequence[no_trace_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> no_trace m) \<Longrightarrow> no_trace (sequence ms)"
  unfolding sequence_def
  by (induct ms; wpsimp wp: no_trace_terminal)

lemma no_trace_sequence_x[no_trace_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> no_trace m) \<Longrightarrow> no_trace (sequence_x ms)"
  unfolding sequence_x_def
  by (induct ms; wpsimp wp: no_trace_terminal)

lemma no_trace_sequenceE[no_trace_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> no_trace m) \<Longrightarrow> no_trace (sequenceE ms)"
  unfolding sequenceE_def
  by (induct ms; wpsimp wp: no_trace_terminal)

lemma no_trace_sequenceE_x[no_trace_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> no_trace m) \<Longrightarrow> no_trace (sequenceE_x ms)"
  unfolding sequenceE_x_def
  by (induct ms; wpsimp wp: no_trace_terminal)

lemma no_trace_mapM_x[no_trace_cond]:
  "(\<And>m. m \<in> f ` set ms \<Longrightarrow> no_trace m) \<Longrightarrow> no_trace (mapM_x f ms)"
  unfolding mapM_x_def
  by (fastforce intro: no_trace_sequence_x)

lemma no_trace_mapME[no_trace_cond]:
  "(\<And>m. m \<in> f ` set xs \<Longrightarrow> no_trace m) \<Longrightarrow> no_trace (mapME f xs)"
  unfolding mapME_def
  by (fastforce intro: no_trace_sequenceE)

lemma no_trace_mapME_x[no_trace_cond]:
  "(\<And>m'. m' \<in> f ` set xs \<Longrightarrow> no_trace m') \<Longrightarrow> no_trace (mapME_x f xs)"
  unfolding mapME_x_def
  by (fastforce intro: no_trace_sequenceE_x)

lemma no_trace_filterM[no_trace_cond]:
  "(\<And>m. m \<in> set ms \<Longrightarrow> no_trace (P m)) \<Longrightarrow> no_trace (filterM P ms)"
  by (induct ms; wpsimp wp: no_trace_terminal split_del: if_split)

lemma no_trace_zipWithM_x[no_trace_cond]:
  "(\<And>x y. no_trace (f x y)) \<Longrightarrow> no_trace (zipWithM_x f xs ys)"
  unfolding zipWithM_x_def zipWith_def
  by (fastforce intro: no_trace_sequence_x)

lemma no_trace_zipWithM[no_trace_cond]:
  "(\<And>x y. no_trace (f x y)) \<Longrightarrow> no_trace (zipWithM f xs ys)"
  unfolding zipWithM_def zipWith_def
  by (fastforce intro: no_trace_sequence)

lemma no_trace_foldM[no_trace_cond]:
  "(\<And>x y. no_trace (m x y)) \<Longrightarrow> no_trace (foldM m xs a)"
  unfolding foldM_def
  by (induct xs; wpsimp wp: no_trace_terminal)

lemma no_trace_foldME[no_trace_cond]:
  "(\<And>x y. no_trace (m x y)) \<Longrightarrow> no_trace (foldME m a xs)"
  unfolding foldME_def
  by (induct xs; wpsimp wp: no_trace_terminal)

lemma no_trace_maybeM[no_trace_cond]:
  "\<forall>x. no_trace (f x) \<Longrightarrow> no_trace (maybeM f t)"
  unfolding maybeM_def
  by (fastforce intro: no_trace_terminal split: option.splits)

lemma no_trace_notM[no_trace_cond]:
  "no_trace A \<Longrightarrow> no_trace (notM A)"
  unfolding notM_def
  by (wpsimp wp: no_trace_terminal)

lemma no_trace_ifM[no_trace_cond]:
  "\<lbrakk> no_trace P; no_trace a; no_trace b \<rbrakk> \<Longrightarrow> no_trace (ifM P a b)"
  unfolding ifM_def by wpsimp

lemma no_trace_ifME[no_trace_cond]:
  "\<lbrakk> no_trace P; no_trace a; no_trace b \<rbrakk> \<Longrightarrow> no_trace (ifME P a b)"
  unfolding ifME_def by wpsimp

lemma no_trace_whenM[no_trace_cond]:
  "\<lbrakk> no_trace P; no_trace f \<rbrakk> \<Longrightarrow> no_trace (whenM P f)"
  unfolding whenM_def
  by (wpsimp wp: no_trace_terminal no_trace_cond)

lemma no_trace_orM[no_trace_cond]:
  "\<lbrakk> no_trace A; no_trace B \<rbrakk> \<Longrightarrow> no_trace (orM A B)"
  unfolding orM_def
  by (wpsimp wp: no_trace_terminal no_trace_cond)

lemma no_trace_andM[no_trace_cond]:
  "\<lbrakk> no_trace A; no_trace B \<rbrakk> \<Longrightarrow> no_trace (andM A B)"
  unfolding andM_def
  by (wpsimp wp: no_trace_terminal no_trace_cond)

\<comment> \<open>While the parallel composition of traceless functions doesn't make much sense, this
   still might be useful to handle trivial goals as part of a proof by contradiction.\<close>
lemma no_trace_parallel[no_trace_cond]:
  "\<lbrakk> no_trace f; no_trace g \<rbrakk> \<Longrightarrow> no_trace (parallel f g)"
  by (fastforce simp: parallel_def2 no_trace_def)

(* not everything [simp] by default, because side conditions can slow down simp a lot *)
lemmas no_trace[wp, intro!] = no_trace_terminal no_trace_cond
lemmas [simp] = no_trace_terminal

end