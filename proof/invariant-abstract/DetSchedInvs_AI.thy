(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DetSchedInvs_AI
imports "$L4V_ARCH/ArchDeterministic_AI"
begin

context begin interpretation Arch .
requalify_facts
  machine_op_lift_machine_times
  machine_ops_last_machine_time
end

lemmas [wp] =
  machine_op_lift_machine_times
  machine_ops_last_machine_time

(* FIXME: move to KHeap_AI *)
global_interpretation do_machine_op: non_heap_op "do_machine_op m"
  by unfold_locales wp

\<comment> \<open>Various lifting rules\<close>

lemma hoare_liftP_ext_pre_conj:
  assumes "\<And>P x. \<lbrace>\<lambda>s. P (f s x) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (f s x)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (f s) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (f s)\<rbrace>"
  apply (rule validI, elim conjE)
  apply (erule rsubst[of P])
  apply (rule ext)
  apply (drule use_valid, rule_tac x=x and P="\<lambda>v. f s x = v" in assms)
   by auto

lemmas hoare_vcg_set_pred_lift_pre_conj =
  hoare_liftP_ext_pre_conj[where f="\<lambda>s x. f x s" and P="\<lambda>f. P {x. f x}" for f P]

lemma hoare_lift_diagonal_pre_conj:
  assumes 1: "\<And>t. \<lbrace>\<lambda>s. P s t \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P s t\<rbrace>"
  assumes 2: "\<And>t. \<lbrace>\<lambda>s. P t s \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P t s\<rbrace>"
  shows "\<lbrace>\<lambda>s. P s s \<and> R s\<rbrace> m \<lbrace>\<lambda> rv s. P s s\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (rule use_valid[OF _ 1], assumption, simp)
  apply (rule use_valid[OF _ 2], assumption, simp)
  done

lemmas hoare_lift_concrete_Pf_pre_conj =
  hoare_lift_diagonal_pre_conj[where P="\<lambda>s t. P (f s) t" for P f]

lemmas hoare_lift_concrete_Pf =
  hoare_lift_concrete_Pf_pre_conj[where R=\<top>, simplified]

lemma hoare_vcg_conj_lift_N_pre_conj:
  assumes "\<lbrace>\<lambda>s. N (P s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q rv s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. N (P' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q' rv s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (P s \<and> P' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q rv s \<and> Q' rv s)\<rbrace>"
  using assms by (cases rule: bool_to_bool_cases[of N]; fastforce simp: valid_def)

lemmas hoare_vcg_conj_lift_N = hoare_vcg_conj_lift_N_pre_conj[where R=\<top>, simplified]

lemma hoare_vcg_disj_lift_N_pre_conj:
  assumes "\<lbrace>\<lambda>s. N (P s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q rv s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. N (P' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q' rv s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (P s \<or> P' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q rv s \<or> Q' rv s)\<rbrace>"
  using assms by (cases rule: bool_to_bool_cases[of N]; fastforce simp: valid_def)

lemmas hoare_vcg_disj_lift_N = hoare_vcg_disj_lift_N_pre_conj[where R=\<top>, simplified]

lemma hoare_vcg_imp_lift_N_pre_conj:
  assumes "\<lbrace>\<lambda>s. \<not> N (P s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> N (Q rv s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. N (P' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q' rv s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (P s \<longrightarrow> P' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q rv s \<longrightarrow> Q' rv s)\<rbrace>"
  using assms by (cases rule: bool_to_bool_cases[of N]; fastforce simp: valid_def)

lemmas hoare_vcg_imp_lift_N = hoare_vcg_imp_lift_N_pre_conj[where R=\<top>, simplified]

lemma hoare_vcg_ball_lift_N_pre_conj:
  assumes "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>\<lambda>s. N (P x s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q x rv s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (\<forall>x\<in>S. P x s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (\<forall>x\<in>S. Q x rv s)\<rbrace>"
  using assms by (cases rule: bool_to_bool_cases[of N]; fastforce simp: valid_def)

lemmas hoare_vcg_ball_lift_N = hoare_vcg_ball_lift_N_pre_conj[where R=\<top>, simplified]

lemmas hoare_vcg_all_lift_N_pre_conj =
  hoare_vcg_ball_lift_N_pre_conj[where S=UNIV, simplified]

lemmas hoare_vcg_all_lift_N = hoare_vcg_all_lift_N_pre_conj[where R=\<top>, simplified]

lemma hoare_vcg_bex_lift_N_pre_conj:
  assumes "\<And>x. \<lbrace>\<lambda>s. N (P x s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (Q x rv s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (\<exists>x\<in>S. P x s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (\<exists>x\<in>S. Q x rv s)\<rbrace>"
  using assms by (cases rule: bool_to_bool_cases[of N]; fastforce simp: valid_def)

lemmas hoare_vcg_bex_lift_N = hoare_vcg_bex_lift_N_pre_conj[where R=\<top>, simplified]

lemmas hoare_vcg_ex_lift_N_pre_conj =
  hoare_vcg_bex_lift_N_pre_conj[where S=UNIV, simplified]

lemmas hoare_vcg_ex_lift_N = hoare_vcg_ex_lift_N_pre_conj[where R=\<top>, simplified]

lemmas hoare_vcg_bex_lift =
  hoare_vcg_bex_lift_N_pre_conj[where N="\<lambda>c. c" and R=\<top>, simplified]

lemma hoare_vcg_ball_lift2_pre_conj:
  assumes "\<And>x. \<lbrace>\<lambda>s. x \<notin> Q s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. x \<notin> Q s\<rbrace>"
  assumes "\<And>x. \<lbrace>\<lambda>s. P x s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P x s\<rbrace>"
  shows "\<lbrace>\<lambda>s. (\<forall>x \<in> Q s. P x s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> Q s. P x s\<rbrace>"
  apply (simp add: Ball_def, rule hoare_vcg_all_lift_N_pre_conj)
  by (wpsimp wp: hoare_vcg_imp_lift' assms)

lemmas hoare_vcg_ball_lift2 = hoare_vcg_ball_lift2_pre_conj[where R=\<top>, simplified]

lemma hoare_vcg_prop_pre_conj:
  "\<lbrace>\<lambda>s. P \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P\<rbrace>"
  by wpsimp

(* FIXME: move to Lib *)
\<comment> \<open>Useful for dealing with heap projections\<close>

definition case_map :: "'c \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where
  "case_map N P m x \<equiv> case_option N P (m x)"

abbreviation "pred_map \<equiv> case_map False"

lemmas pred_map_def2 = case_map_def[of False]

lemma pred_map_def:
  "pred_map P m x \<longleftrightarrow> (\<exists>y. m x = Some y \<and> P y)"
  by (simp add: pred_map_def2 split: option.splits)

\<comment> \<open>We use a separate constant for object equality assertions,
    to get nicer simplification rules.\<close>
definition pred_map_eq :: "'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> bool" where
  "pred_map_eq x \<equiv> pred_map ((=) x)"

lemma pred_map_eq_normalise:
  "pred_map ((=) x) = pred_map_eq x"
  "pred_map (\<lambda>y. y = x) = pred_map_eq x"
  by (fastforce simp: pred_map_eq_def pred_map_def)+

lemma pred_map_eq:
  "pred_map_eq y m x \<longleftrightarrow> m x = Some y"
  by (auto simp: pred_map_eq_def pred_map_def)

lemmas pred_map_simps = pred_map_eq pred_map_def

lemma opt_map_None:
  "(f |> g) x = None \<longleftrightarrow> f x = None \<or> (\<exists>y. f x = Some y \<and> g y = None)"
  by (simp add: opt_map_def split: option.splits)

lemmas opt_map_Some = in_opt_map_eq
lemmas opt_map_simps = opt_map_None opt_map_Some

definition map_project :: "('c \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'c) \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "map_project f m x \<equiv> map_option f (m x)"

lemma map_project_None:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "map_project f m x = None \<longleftrightarrow> m x = None"
  by (simp add: map_project_def)

lemma map_project_Some:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "map_project f m x = Some z \<longleftrightarrow> (\<exists>y. m x = Some y \<and> f y = z)"
  by (auto simp: map_project_def)

lemmas map_project_simps = map_project_None map_project_Some

lemma pred_map_map_project:
  "pred_map P (map_project proj m) x \<longleftrightarrow> (\<exists>y. m x = Some y \<and> P (proj y))"
  by (auto simp: pred_map_def map_project_simps)

definition map_join :: "('a \<rightharpoonup> 'b option) \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "map_join m = m |> id"

lemma map_join_None':
  "map_join m x = None \<longleftrightarrow> m x = None \<or> m x = Some None"
  by (simp add: map_join_def opt_map_simps)

lemma map_join_None:
  "map_join m x = None \<longleftrightarrow> (\<forall>y. m x \<noteq> Some (Some y))"
  by (cases "m x"; simp add: map_join_None')

lemma map_join_Some:
  "map_join m x = Some y \<longleftrightarrow> m x = Some (Some y)"
  by (simp add: map_join_def opt_map_simps)

lemmas map_join_simps = map_join_None map_join_Some

lemma map_eqI:
  assumes "\<And>x. m x = None \<longleftrightarrow> m' x = None"
  assumes "\<And>x y. m x = Some y \<longleftrightarrow> m' x = Some y"
  shows "m = m'"
  by (rule ext; case_tac "m x"; simp add: assms)

lemma pred_map_map_eqI:
  assumes "\<And>P x. pred_map P m' x = pred_map P m x"
  shows "m' = m"
  apply (rule map_eqI)
   apply (cut_tac x=x and P=\<top> in assms, drule arg_cong_Not, clarsimp simp: pred_map_simps)
  apply (cut_tac x=x and P="(=) y" in assms, clarsimp simp: pred_map_simps)
  done

lemma pred_map_pred_conj:
  "pred_map (P and Q) h s = (pred_map P h s \<and> pred_map Q h s)"
  by (clarsimp simp: pred_map_simps, fastforce)

lemma map_project_id:
  "map_project (\<lambda>x. x) m = m"
  by (rule ext, auto simp: map_project_def option.map_ident)

lemma map_project_map_eqI:
  assumes"map_project (\<lambda>x. x) m' = map_project (\<lambda>x. x) m"
  shows "m' = m"
  by (rule assms[simplified map_project_id])

lemma pred_map_map_join:
  "pred_map P (map_join m) = pred_map (\<lambda>y. \<exists>z. y = Some z \<and> P z) m"
  by (fastforce simp: pred_map_simps map_join_simps)

lemma pred_map_eq_map_join:
  "pred_map_eq x (map_join m) = pred_map_eq (Some x) m"
  by (fastforce simp: pred_map_simps map_join_simps)

lemma pred_map_compose:
  "pred_map (P \<circ> f) = pred_map P \<circ> map_project f"
  by (fastforce simp: pred_map_simps map_project_simps)

lemma map_project_compose:
  "map_project f (map_project g m) = map_project (f \<circ> g) m"
  by (fastforce simp: map_project_def map_option_comp2)

lemma map_project_opt_map:
  "map_project f (m |> k) = m |> map_project f k"
  by (fastforce simp: map_project_def opt_map_def split: option.splits)

abbreviation pred_map' :: "('b \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b option) \<Rightarrow> 'a \<Rightarrow> bool" where
  "pred_map' P hp \<equiv> pred_map P (map_join hp)"

\<comment> \<open>Chained references between two heaps\<close>
abbreviation pred_map2 ::
  "('obj \<Rightarrow> bool) \<Rightarrow> ('ref \<rightharpoonup> 'chain) \<Rightarrow> ('chain \<rightharpoonup> 'obj) \<Rightarrow> 'ref \<Rightarrow> bool"
  where
  "pred_map2 P hp hp' \<equiv> pred_map P (hp |> hp')"

lemma pred_map2_def:
  "pred_map2 P hp hp' ref \<equiv>
    \<exists>ref' obj. hp ref = Some ref' \<and> hp' ref' = Some obj \<and> P obj"
  by (auto simp: atomize_eq pred_map_simps map_join_simps opt_map_simps)

lemma pred_map2_pred_maps:
  "pred_map2 P hp hp' = (\<lambda>ref. \<exists>ref'. pred_map_eq ref' hp ref \<and> pred_map P hp' ref')"
  by (fastforce simp add: atomize_eq pred_map_simps opt_map_simps)

abbreviation pred_map2' ::
  "('obj \<Rightarrow> bool) \<Rightarrow> ('ref \<rightharpoonup> 'chain option) \<Rightarrow> ('chain \<Rightarrow> 'obj option) \<Rightarrow> 'ref \<Rightarrow> bool"
  where
  "pred_map2' P hp \<equiv> pred_map2 P (map_join hp)"

lemmas pred_map2'_def =
  pred_map2_def[where hp="map_join hp" for hp, simplified map_join_simps]

lemmas pred_map2'_pred_maps =
  pred_map2_pred_maps[where hp="map_join hp" for hp, simplified pred_map_eq_map_join]

lemma pred_map2_conj:
  "pred_map2 (\<lambda>x. P x \<and> Q x) m m' x \<longleftrightarrow> pred_map2 P m m' x \<and> pred_map2 Q m m' x"
  by (auto simp: pred_map_simps opt_map_simps)

lemma pred_map_upd:
  "pred_map P (\<lambda>r. if r = ref then v else m r)
   = (\<lambda>x. if x = ref then \<exists>y. v = Some y \<and> P y else pred_map P m x)"
  by (auto simp: pred_map_simps)

lemma pred_map_updupd:
  "pred_map P (\<lambda>r. if r = ref then v else if r = ref' then v' else m r)
   = (\<lambda>x. if x = ref
          then (\<exists>y. v = Some y \<and> P y)
          else (if x = ref' then (\<exists>y. v' = Some y \<and> P y) else pred_map P m x))"
  by (rule ext, auto simp: pred_map_simps)

lemma pred_map_eq_upd:
  "pred_map_eq w (\<lambda>r. if r = ref then v else m r)
   = (\<lambda>x. if x = ref then v = Some w else pred_map_eq w m x)"
  by (auto simp: pred_map_simps)

lemma pred_map_eq_updupd:
  "pred_map_eq w (\<lambda>r. if r = ref then v else if r = ref' then v' else m r)
   = (\<lambda>x. if x = ref then (v = Some w) else (if x = ref' then (v' = Some w) else pred_map_eq w m x))"
  by (rule ext, auto simp: pred_map_simps)

lemma pred_map2_upd1:
  "pred_map2 P (\<lambda>r. if r = ref then v else m r) m'
   = (\<lambda>x. if x = ref then \<exists>w. v = Some w \<and> pred_map P m' w else pred_map2 P m m' x)"
  by (fastforce simp add: pred_map_simps opt_map_simps split: if_splits)

lemma pred_map2'_upd1:
  "pred_map2' P (\<lambda>r. if r = ref then v else m r) m'
   = (\<lambda>x. if x = ref then \<exists>w. v = Some (Some w) \<and> pred_map P m' w else pred_map2' P m m' x)"
  by (fastforce simp add: pred_map_simps map_join_simps opt_map_simps split: if_splits)

lemmas pred_map_upds =
  pred_map_upd pred_map_eq_upd

lemma map_project_upd:
  "map_project f (\<lambda>r. if r = ref then v else m r)
   = (\<lambda>x. if x = ref then map_option f v else map_project f m x)"
  by (auto simp: map_project_def)

lemma opt_map_upd1:
  "((\<lambda>r. if r = ref then v else m r) |> f)
   = (\<lambda>x. if x = ref then case_option None f v else (m |> f) x)"
  by (auto simp: opt_map_def)

\<comment> \<open>Locales for generating boilerplate rules from definitions of map projections.
    These allow us to replicate various generic heap combinator rules for defined constants,
    and give cleaner (and more automation-friendly) simplification rules for certain constructions.
    These locales have become a bit more unwieldy than I would have liked.\<close>

locale opt_map_def_locale =
  fixes ref_type :: "'ref itself"
  fixes k :: "'a \<rightharpoonup> 'b"
  fixes c :: "('ref \<rightharpoonup> 'a) \<Rightarrow> ('ref \<rightharpoonup> 'b)"
  assumes proj_def: "c m \<equiv> m |> k"
begin

lemma pred_map_simps:
  "pred_map_eq z (c m) = (\<lambda>x. \<exists>y. m x = Some y \<and> k y = Some z)"
  "pred_map P (c m) = (\<lambda>x. \<exists>y z. m x = Some y \<and> k y = Some z \<and> P z)"
  by (fastforce simp: pred_map_simps proj_def opt_map_simps)+

lemmas pred_map_upds =
  pred_map_upds[where m="c m" for m]

lemma simps:
  shows None: "c m x = None \<longleftrightarrow> m x = None \<or> (\<exists>y. m x = Some y \<and> k y = None)"
    and Some: "c m x = Some z \<longleftrightarrow> (\<exists>y. m x = Some y \<and> k y = Some z)"
  by (auto simp: proj_def opt_map_simps)

lemma upd:
  "c (\<lambda>r. if r = ref then v else m r)
   = (\<lambda>x. if x = ref then case_option None k v else c m x)"
  by (simp add: proj_def opt_map_upd1)

lemma upd_idem:
  assumes "case_option None k (m ref) = v"
  shows "(if x = ref then v else c m x) = c m x"
  by (auto simp: proj_def assms opt_map_def)

lemmas all_simps = pred_map_simps pred_map_upds upd simps upd_idem

end

locale map_project_def_locale =
  fixes ref_type :: "'ref itself"
  fixes f :: "'a \<Rightarrow> 'b"
  fixes p :: "('ref \<rightharpoonup> 'a) \<Rightarrow> ('ref \<rightharpoonup> 'b)"
  assumes proj_def: "p \<equiv> map_project f"
begin

lemma pred_map_simps:
  "pred_map_eq z (p m) = (\<lambda>x. \<exists>y. m x = Some y \<and> f y = z)"
  "pred_map P (p m) = (\<lambda>x. \<exists>y. m x = Some y \<and> P (f y))"
  by (fastforce simp: pred_map_simps proj_def map_project_simps)+

lemmas pred_map_upds =
  pred_map_upds[where m="p m" for m]

lemma simps:
  shows None: "p m x = None \<longleftrightarrow> m x = None"
    and Some: "p m x = Some z \<longleftrightarrow> (\<exists>y. m x = Some y \<and> f y = z)"
  by (auto simp: proj_def map_project_simps)

lemma upd:
  "p (\<lambda>r. if r = ref then v else m r)
    = (\<lambda>x. if x = ref then map_option f v else p m x)"
  by (simp add: proj_def map_project_upd)

lemma upd_idem:
  assumes "map_option f (m ref) = v"
  shows "(if x = ref then v else p m x) = p m x"
  by (auto simp: proj_def assms map_project_def)

lemmas all_simps = pred_map_simps pred_map_upds upd simps upd_idem

end

locale map_project_opt_map_def_locale =
  c: opt_map_def_locale ref_type k c +
  p: map_project_def_locale ref_type f p
  for ref_type :: "'ref itself"
  and k :: "'a \<rightharpoonup> 'b"
  and c :: "('ref \<rightharpoonup> 'a) \<Rightarrow> ('ref \<rightharpoonup> 'b)"
  and f :: "'b \<Rightarrow> 'c"
  and p :: "('ref \<rightharpoonup> 'b) \<Rightarrow> ('ref \<rightharpoonup> 'c)"
begin

lemma pred_map_simps:
  "pred_map_eq v (p (c m)) = (\<lambda>x. \<exists>y z. m x = Some y \<and> k y = Some z \<and> f z = v)"
  "pred_map P (p (c m)) = (\<lambda>x. \<exists>y z. m x = Some y \<and> k y = Some z \<and> P (f z))"
  by (auto simp add: p.pred_map_simps c.simps)

lemmas pred_map_upds =
  pred_map_upds[where m="p (c m)" for m]

lemma simps:
  shows None: "p (c m) x = None \<longleftrightarrow> m x = None \<or> (\<exists>y. m x = Some y \<and> k y = None)"
    and Some: "p (c m) x = Some v \<longleftrightarrow> (\<exists>y z. m x = Some y \<and> k y = Some z \<and> f z = v)"
  by (auto simp add: p.simps c.simps)

lemma upd:
  "p (c (\<lambda>r. if r = ref then v else m r))
   = (\<lambda>x. if x = ref then Option.bind v (\<lambda>y. map_option f (k y)) else p (c m) x)"
  by (auto simp: c.upd p.upd split: option.splits if_splits)

lemma upd_idem:
  assumes "map_option f (case_option None k (m ref)) = v"
  shows "(if x = ref then v else p (c m) x) = p (c m) x"
  by (auto simp: p.proj_def c.proj_def assms map_project_def opt_map_def)

lemmas proj_def = p.proj_def
lemmas all_simps = pred_map_simps pred_map_upds upd simps upd_idem

end

locale opt_map_cons_def_locale =
  c: opt_map_def_locale ref_type k c
  for ref_type :: "'ref itself"
  and k :: "'a \<rightharpoonup> 'b"
  and c :: "('ref \<rightharpoonup> 'a) \<Rightarrow> ('ref \<rightharpoonup> 'b)" +
  fixes C :: "'b \<Rightarrow> 'a"
  assumes k_None: "\<And>a. k a = None \<longleftrightarrow> (\<forall>b. a \<noteq> C b)"
  assumes k_Some: "\<And>a b. k a = Some b \<longleftrightarrow> a = C b"
begin

lemma pred_map_simps:
  "pred_map_eq y (c m) = (\<lambda>x. m x = Some (C y))"
  "pred_map P (c m) = (\<lambda>x. \<exists>y. m x = Some (C y) \<and> P y)"
  by (auto simp: c.pred_map_simps k_Some)

lemma simps:
  shows None: "c m x = None \<longleftrightarrow> (\<forall>y. m x \<noteq> Some (C y))"
    and Some: "c m x = Some y \<longleftrightarrow> m x = Some (C y)"
  by (cases "m x") (auto simp: c.proj_def opt_map_simps k_None k_Some)

lemmas upd = c.upd
lemmas upd_idem = c.upd_idem
lemmas proj_def = c.proj_def
lemmas pred_map_upds = c.pred_map_upds
lemmas all_simps = pred_map_simps pred_map_upds upd simps upd_idem

end

\<comment> \<open>For kernel object constructors that carry some extra information that we mostly ignore.\<close>
locale opt_map_cons2_def_locale =
  c: opt_map_def_locale ref_type k c
  for ref_type :: "'ref itself"
  and k :: "'a \<rightharpoonup> 'b"
  and c :: "('ref \<rightharpoonup> 'a) \<Rightarrow> ('ref \<rightharpoonup> 'b)" +
  fixes C :: "'b \<Rightarrow> 'e \<Rightarrow> 'a"
  assumes k_None: "\<And>a. k a = None \<longleftrightarrow> (\<forall>b e. a \<noteq> C b e)"
  assumes k_Some: "\<And>a b. k a = Some b \<longleftrightarrow> (\<exists>e. a = C b e)"
begin

lemma pred_map_simps:
  "pred_map_eq y (c m) = (\<lambda>x. \<exists>e. m x = Some (C y e))"
  "pred_map P (c m) = (\<lambda>x. \<exists>y e. m x = Some (C y e) \<and> P y)"
  by (auto simp: c.pred_map_simps k_Some)

lemma simps:
  shows None: "c m x = None \<longleftrightarrow> (\<forall>y e. m x \<noteq> Some (C y e))"
    and Some: "c m x = Some y \<longleftrightarrow> (\<exists>e. m x = Some (C y e))"
  by (cases "m x") (auto simp: c.proj_def opt_map_simps k_None k_Some)

lemmas upd = c.upd
lemmas upd_idem = c.upd_idem
lemmas proj_def = c.proj_def
lemmas pred_map_upds = c.pred_map_upds
lemmas all_simps = pred_map_simps pred_map_upds upd simps upd_idem

end

locale map_project_opt_map_cons_def_locale =
  c: opt_map_cons_def_locale ref_type k c C +
  p: map_project_opt_map_def_locale ref_type k c f p
  for ref_type :: "'ref itself"
  and k :: "'a \<rightharpoonup> 'b"
  and c :: "('ref \<rightharpoonup> 'a) \<Rightarrow> ('ref \<rightharpoonup> 'b)"
  and C :: "'b \<Rightarrow> 'a"
  and f :: "'b \<Rightarrow> 'c"
  and p :: "('ref \<rightharpoonup> 'b) \<Rightarrow> ('ref \<rightharpoonup> 'c)"
begin

lemma pred_map_simps:
  "pred_map_eq v (p (c m)) = (\<lambda>x. \<exists>y. m x = Some (C y) \<and> f y = v)"
  "pred_map P (p (c m)) = (\<lambda>x. \<exists>y. m x = Some (C y) \<and> P (f y))"
  by (fastforce simp: p.pred_map_simps c.simps c.k_Some)+

lemma simps:
  shows None: "p (c m) x = None \<longleftrightarrow> (\<forall>b. m x \<noteq> Some (C b))"
    and Some: "p (c m) x = Some y \<longleftrightarrow> (\<exists>b. m x = Some (C b) \<and> f b = y)"
  by (cases "m x") (auto simp: p.simps c.k_None c.k_Some)

lemmas upd = p.upd
lemmas upd_idem = p.upd_idem
lemmas proj_def = p.proj_def
lemmas pred_map_upds = p.pred_map_upds
lemmas all_simps = pred_map_simps pred_map_upds upd simps upd_idem

end

locale map_project_opt_map_cons2_def_locale =
  c: opt_map_cons2_def_locale ref_type k c C +
  p: map_project_opt_map_def_locale ref_type k c f p
  for ref_type :: "'ref itself"
  and k :: "'a \<rightharpoonup> 'b"
  and c :: "('ref \<rightharpoonup> 'a) \<Rightarrow> ('ref \<rightharpoonup> 'b)"
  and C :: "'b \<Rightarrow> 'e \<Rightarrow> 'a"
  and f :: "'b \<Rightarrow> 'c"
  and p :: "('ref \<rightharpoonup> 'b) \<Rightarrow> ('ref \<rightharpoonup> 'c)"
begin

lemma pred_map_simps:
  "pred_map_eq v (p (c m)) = (\<lambda>x. \<exists>y e. m x = Some (C y e) \<and> f y = v)"
  "pred_map P (p (c m)) = (\<lambda>x. \<exists>y e. m x = Some (C y e) \<and> P (f y))"
  by (fastforce simp add: p.pred_map_simps c.simps c.k_Some)+

lemma simps:
  shows None: "p (c m) x = None \<longleftrightarrow> (\<forall>b e. m x \<noteq> Some (C b e))"
    and Some: "p (c m) x = Some y \<longleftrightarrow> (\<exists>b e. m x = Some (C b e) \<and> f b = y)"
  by (cases "m x") (auto simp: p.simps c.k_None c.k_Some)

lemmas upd = p.upd
lemmas upd_idem = p.upd_idem
lemmas proj_def = p.proj_def
lemmas pred_map_upds = p.pred_map_upds
lemmas all_simps = pred_map_simps pred_map_upds upd simps upd_idem

end

locale opt_map_opt_map_cons_def_locale =
  c: opt_map_cons_def_locale ref_type k c C +
  p: opt_map_cons_def_locale ref_type f p F
  for ref_type :: "'ref itself"
  and k :: "'a \<rightharpoonup> 'b"
  and c :: "('ref \<rightharpoonup> 'a) \<Rightarrow> ('ref \<rightharpoonup> 'b)"
  and C :: "'b \<Rightarrow> 'a"
  and f :: "'b \<rightharpoonup> 'c"
  and F :: "'c \<Rightarrow> 'b"
  and p :: "('ref \<rightharpoonup> 'b) \<Rightarrow> ('ref \<rightharpoonup> 'c)"
begin

lemmas pred_map_upds =
  pred_map_upds[where m="p (c m)" for m]

lemma pred_map_simps:
  "pred_map_eq v (p (c m)) = (\<lambda>x. m x = Some (C (F v)))"
  "pred_map P (p (c m)) = (\<lambda>x. \<exists>y. m x = Some (C (F y)) \<and> P y)"
  by (auto simp: p.pred_map_simps c.simps c.k_Some)+

lemma simps:
  shows None: "p (c m) x = None \<longleftrightarrow> (\<forall>b. m x \<noteq> Some (C (F b)))"
    and Some: "p (c m) x = Some v \<longleftrightarrow> (m x = Some (C (F v)))"
  by (auto simp add: p.simps c.simps)

lemma upd:
  "p (c (\<lambda>r. if r = ref then v else m r))
   = (\<lambda>x. if x = ref then Option.bind v (\<lambda>y. Option.bind (k y) f) else p (c m) x)"
  by (auto simp: c.upd p.upd split: option.splits if_splits)

lemma upd_idem:
  assumes "case_option None f (case_option None k (m ref)) = v"
  shows "(if x = ref then v else p (c m) x) = p (c m) x"
  by (auto simp: p.proj_def c.proj_def assms map_project_def opt_map_def)

lemmas proj_def = p.proj_def
lemmas all_simps = pred_map_simps pred_map_upds upd simps upd_idem

end

\<comment> \<open>Project threads from the kernel heap\<close>

definition tcb_of :: "kernel_object \<rightharpoonup> tcb" where
  "tcb_of ko \<equiv> case ko of TCB tcb \<Rightarrow> Some tcb | _ \<Rightarrow> None"

lemma tcb_of_simps:
  "tcb_of (TCB tcb) = Some tcb"
  "tcb_of (SchedContext sc n) = None"
  "tcb_of (CNode n cnode) = None"
  "tcb_of (Endpoint ep) = None"
  "tcb_of (Notification ntfn) = None"
  "tcb_of (Reply reply) = None"
  "tcb_of (ArchObj aobj) = None"
  by (auto simp: tcb_of_def)

lemma tcb_of_Some:
  "tcb_of ko = Some tcb \<longleftrightarrow> ko = TCB tcb"
  by (simp add: tcb_of_def split: kernel_object.splits)

lemma tcb_of_None:
  "tcb_of ko = None \<longleftrightarrow> (\<forall>tcb. ko \<noteq> TCB tcb)"
  by (simp add: tcb_of_def split: kernel_object.splits)

definition tcbs_of_kh :: "('obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> 'obj_ref \<rightharpoonup> tcb" where
  "tcbs_of_kh kh \<equiv> kh |> tcb_of"

abbreviation tcbs_of :: "'z state \<Rightarrow> obj_ref \<rightharpoonup> tcb" where
  "tcbs_of s \<equiv> tcbs_of_kh (kheap s)"

lemmas tcb_heap_of_state_def = tcbs_of_kh_def[of "kheap s" for s :: "'z state"]

global_interpretation tcb_heap: opt_map_cons_def_locale _ tcb_of tcbs_of_kh TCB
  using tcbs_of_kh_def tcb_of_Some tcb_of_None by unfold_locales

\<comment> \<open>Project tcb thread state field\<close>

definition tcb_sts_of_tcbs :: "('obj_ref \<rightharpoonup> tcb) \<Rightarrow> 'obj_ref \<rightharpoonup> thread_state" where
  "tcb_sts_of_tcbs \<equiv> map_project tcb_state"

abbreviation "tcb_sts_of_kh kh \<equiv> tcb_sts_of_tcbs (tcbs_of_kh kh)"
abbreviation "tcb_sts_of s \<equiv> tcb_sts_of_kh (kheap s)"

global_interpretation tcb_sts:
  map_project_opt_map_cons_def_locale _ tcb_of tcbs_of_kh TCB tcb_state tcb_sts_of_tcbs
  using tcb_sts_of_tcbs_def by unfold_locales

\<comment> \<open>Project tcb scheduling context pointer field\<close>

definition tcb_scps_of_tcbs :: "('obj_ref \<rightharpoonup> tcb) \<Rightarrow> 'obj_ref \<rightharpoonup> obj_ref option" where
  "tcb_scps_of_tcbs \<equiv> map_project tcb_sched_context"

abbreviation "tcb_scps_of_kh kh \<equiv> tcb_scps_of_tcbs (tcbs_of_kh kh)"
abbreviation "tcb_scps_of s \<equiv> tcb_scps_of_kh (kheap s)"

global_interpretation tcb_scps:
  map_project_opt_map_cons_def_locale _ tcb_of tcbs_of_kh TCB tcb_sched_context tcb_scps_of_tcbs
  using tcb_scps_of_tcbs_def by unfold_locales

\<comment> \<open>Project tcb fault field\<close>

definition tcb_faults_of_tcbs :: "('obj_ref \<rightharpoonup> tcb) \<Rightarrow> 'obj_ref \<rightharpoonup> fault option" where
  "tcb_faults_of_tcbs \<equiv> map_project tcb_fault"

abbreviation "tcb_faults_of_kh kh \<equiv> tcb_faults_of_tcbs (tcbs_of_kh kh)"
abbreviation "tcb_faults_of s \<equiv> tcb_faults_of_kh (kheap s)"

global_interpretation tcb_faults:
  map_project_opt_map_cons_def_locale _ tcb_of tcbs_of_kh TCB tcb_fault tcb_faults_of_tcbs
  using tcb_faults_of_tcbs_def by unfold_locales

\<comment> \<open>FIXME: add these to the boilerplate generation locales,
           and perhaps give the two lemmas separate names.\<close>
lemmas pred_tcb_scps_of_kh_simps =
  pred_map2'_pred_maps[where hp="tcb_scps_of_kh kh" and hp'=sc_heap for kh and sc_heap
                       , simplified pred_map_eq_map_join]
  pred_map2'_upd1[where m="tcb_scps_of_kh kh" and m'=sc_heap for kh and sc_heap]

\<comment> \<open>Project etcbs. These records originally made up the "extended kheap" used in the
    deterministic version of the specification. For MCS, they are now part of tcb objects
    in the main kheap. We project them together, since they are typically used together.\<close>

record etcb =
  etcb_priority :: "priority"
  etcb_domain :: "domain"

definition etcb_of :: "tcb \<Rightarrow> etcb" where
  "etcb_of t = \<lparr> etcb_priority = tcb_priority t, etcb_domain = tcb_domain t \<rparr>"

definition etcbs_of_tcbs :: "('obj_ref \<rightharpoonup> tcb) \<Rightarrow> 'obj_ref \<rightharpoonup> etcb" where
  "etcbs_of_tcbs \<equiv> map_project etcb_of"

abbreviation "etcbs_of_kh kh \<equiv> etcbs_of_tcbs (tcbs_of_kh kh)"
abbreviation "etcbs_of s \<equiv> etcbs_of_kh (kheap s)"

global_interpretation etcbs:
  map_project_opt_map_cons_def_locale _ tcb_of tcbs_of_kh TCB etcb_of etcbs_of_tcbs
  using etcbs_of_tcbs_def by unfold_locales

lemma etcb_of_simps[iff]:
  "etcb_priority (etcb_of tcb) = tcb_priority tcb"
  "etcb_domain (etcb_of tcb) = tcb_domain tcb"
  by (auto simp: etcb_of_def)

\<comment> \<open>These might not be necessary, since they're already solved by auto\<close>
lemma etcb_of_updates[iff]:
  "\<And>f. etcb_of (tcb_ctable_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_vtable_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_ipcframe_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_fault_handler_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_timeout_handler_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_state_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_ipc_buffer_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_fault_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_bound_notification_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_mcpriority_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_sched_context_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_yield_to_update f tcb) = etcb_of tcb"
  "\<And>f. etcb_of (tcb_priority_update f tcb) = etcb_priority_update f (etcb_of tcb)"
  "\<And>f. etcb_of (tcb_domain_update f tcb) = etcb_domain_update f (etcb_of tcb)"
  "\<And>f. etcb_of (tcb_arch_update f tcb) = etcb_of tcb"
  by auto

\<comment> \<open>For compatibility with old proofs: etcb_at is trivially preserved by object deletion\<close>

definition etcb_at' where
  "etcb_at' P etcbs ref \<equiv> pred_map \<top> etcbs ref \<longrightarrow> pred_map P etcbs ref"

abbreviation "etcb_at P ref s \<equiv> etcb_at' P (etcbs_of s) ref"

lemmas etcb_at_def = etcb_at'_def[where etcbs="etcbs_of s" for s :: "'z state"]

lemma pred_map_etcb_at:
  "pred_map P etcbs ref \<Longrightarrow> etcb_at' P etcbs ref"
  by (simp add: etcb_at'_def)

lemma etcb_at'_pred_map:
  "\<lbrakk> etcb_at' P etcbs ref; pred_map \<top> etcbs ref \<rbrakk> \<Longrightarrow> pred_map P etcbs ref"
  by (simp add: etcb_at'_def)

\<comment> \<open>Project scheduling contexts from the kernel heap\<close>

definition sc_of :: "kernel_object \<rightharpoonup> sched_context" where
  "sc_of ko \<equiv> case ko of SchedContext sc n \<Rightarrow> Some sc | _ \<Rightarrow> None"

lemma sc_of_simps:
  "sc_of (SchedContext sc n) = Some sc"
  "sc_of (CNode n cnode) = None"
  "sc_of (TCB tcb) = None"
  "sc_of (Endpoint ep) = None"
  "sc_of (Notification ntfn) = None"
  "sc_of (Reply reply) = None"
  "sc_of (ArchObj aobj) = None"
  by (auto simp: sc_of_def)

lemma sc_of_Some:
  "sc_of ko = Some sc \<longleftrightarrow> (\<exists>n. ko = SchedContext sc n)"
  by (simp add: sc_of_def split: kernel_object.splits)

lemma sc_of_None:
  "sc_of ko = None \<longleftrightarrow> (\<forall>sc n. ko \<noteq> SchedContext sc n)"
  by (simp add: sc_of_def split: kernel_object.splits)

definition scs_of_kh :: "('obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> 'obj_ref \<rightharpoonup> sched_context" where
  "scs_of_kh kh \<equiv> kh |> sc_of"

abbreviation scs_of :: "'z state \<Rightarrow> obj_ref \<rightharpoonup> sched_context" where
  "scs_of s \<equiv> scs_of_kh (kheap s)"

lemmas sc_heap_of_state_def = scs_of_kh_def[of "kheap s" for s :: "'z state"]

global_interpretation sc_heap: opt_map_cons2_def_locale _ sc_of scs_of_kh SchedContext
  using scs_of_kh_def sc_of_None sc_of_Some by unfold_locales

\<comment> \<open>Project various fields relevant to managing scheduling contexts refills.
    We project them together, since they are typically used together.
    Why project at all? This allows us to ignore changes to other fields,
    most notably sc_tcb and sc_replies.\<close>

record sc_refill_cfg =
  scrc_refills :: "refill list"
  scrc_refill_max :: nat
  scrc_period :: ticks
  scrc_budget :: ticks

abbreviation
  "scrc_refill_hd scrc \<equiv> hd (scrc_refills scrc)"

definition sc_refill_cfg_of :: "sched_context \<Rightarrow> sc_refill_cfg" where
  "sc_refill_cfg_of sc = \<lparr> scrc_refills = sc_refills sc,
                           scrc_refill_max = sc_refill_max sc,
                           scrc_period = sc_period sc,
                           scrc_budget = sc_budget sc\<rparr>"

definition sc_refill_cfgs_of_scs :: "('obj_ref \<rightharpoonup> sched_context) \<Rightarrow> 'obj_ref \<rightharpoonup> sc_refill_cfg" where
  "sc_refill_cfgs_of_scs \<equiv> map_project sc_refill_cfg_of"

abbreviation "sc_refill_cfgs_of_kh kh \<equiv> sc_refill_cfgs_of_scs (scs_of_kh kh)"
abbreviation "sc_refill_cfgs_of s \<equiv> sc_refill_cfgs_of_kh (kheap s)"

global_interpretation sc_refill_cfgs:
  map_project_opt_map_cons2_def_locale _ sc_of scs_of_kh SchedContext sc_refill_cfg_of sc_refill_cfgs_of_scs
  using sc_refill_cfgs_of_scs_def by unfold_locales

lemma sc_refill_cfg_of_simps[iff]:
  "scrc_refills (sc_refill_cfg_of sc) = sc_refills sc"
  "scrc_refill_max (sc_refill_cfg_of sc) = sc_refill_max sc"
  "scrc_period (sc_refill_cfg_of sc) = sc_period sc"
  "scrc_refill_hd (sc_refill_cfg_of sc) = refill_hd sc"
  "scrc_budget (sc_refill_cfg_of sc) = sc_budget sc"
  by (auto simp: sc_refill_cfg_of_def)

\<comment> \<open>These might not be necessary, since they're already solved by auto\<close>
lemma sc_refill_cfg_of_updates[iff]:
  "\<And>f. sc_refill_cfg_of (sc_period_update f sc) = scrc_period_update f (sc_refill_cfg_of sc)"
  "\<And>f. sc_refill_cfg_of (sc_consumed_update f sc) = sc_refill_cfg_of sc"
  "\<And>f. sc_refill_cfg_of (sc_tcb_update f sc) = sc_refill_cfg_of sc"
  "\<And>f. sc_refill_cfg_of (sc_ntfn_update f sc) = sc_refill_cfg_of sc"
  "\<And>f. sc_refill_cfg_of (sc_refills_update f sc) = scrc_refills_update f (sc_refill_cfg_of sc)"
  "\<And>f. sc_refill_cfg_of (sc_refill_max_update f sc) = scrc_refill_max_update f (sc_refill_cfg_of sc)"
  "\<And>f. sc_refill_cfg_of (sc_badge_update f sc) = sc_refill_cfg_of sc"
  "\<And>f. sc_refill_cfg_of (sc_sporadic_update f sc) = sc_refill_cfg_of sc"
  "\<And>f. sc_refill_cfg_of (sc_yield_from_update f sc) = sc_refill_cfg_of sc"
  "\<And>f. sc_refill_cfg_of (sc_replies_update f sc) = sc_refill_cfg_of sc"
  by auto

abbreviation "sc_refill_cfg_sc_at \<equiv> sc_at_ppred sc_refill_cfg_of"
lemmas sc_refill_cfg_sc_at_def = sc_at_ppred_def[of sc_refill_cfg_of]

\<comment> \<open>Project sc_tcb field\<close>

definition sc_tcbs_of_scs :: "('obj_ref \<rightharpoonup> sched_context) \<Rightarrow> 'obj_ref \<rightharpoonup> obj_ref option" where
  "sc_tcbs_of_scs \<equiv> map_project sc_tcb"

abbreviation "sc_tcbs_of_kh kh \<equiv> sc_tcbs_of_scs (scs_of_kh kh)"
abbreviation "sc_tcbs_of s \<equiv> sc_tcbs_of_kh (kheap s)"

global_interpretation sc_tcbs:
  map_project_opt_map_cons2_def_locale _ sc_of scs_of_kh SchedContext sc_tcb sc_tcbs_of_scs
  using sc_tcbs_of_scs_def by unfold_locales

\<comment> \<open>Project sc_replies field\<close>

definition sc_replies_of_scs :: "('obj_ref \<rightharpoonup> sched_context) \<Rightarrow> 'obj_ref \<rightharpoonup> obj_ref list" where
  "sc_replies_of_scs \<equiv> map_project sc_replies"

abbreviation "sc_replies_of_kh kh \<equiv> sc_replies_of_scs (scs_of_kh kh)"
abbreviation "sc_replies_of s \<equiv> sc_replies_of_kh (kheap s)"

global_interpretation sc_replies:
  map_project_opt_map_cons2_def_locale _ sc_of scs_of_kh SchedContext sc_replies sc_replies_of_scs
  using sc_replies_of_scs_def by unfold_locales

\<comment> \<open>Endpoints\<close>

\<comment> \<open>Project endpoints from the kernel heap\<close>

definition ep_of :: "kernel_object \<rightharpoonup> endpoint" where
  "ep_of ko \<equiv> case ko of Endpoint endpoint \<Rightarrow> Some endpoint | _ \<Rightarrow> None"

definition send_q_of :: "endpoint \<rightharpoonup> obj_ref list" where
  "send_q_of endpoint \<equiv> case endpoint of SendEP q  \<Rightarrow> Some q | _ \<Rightarrow> None"

definition recv_q_of :: "endpoint \<rightharpoonup> obj_ref list" where
  "recv_q_of endpoint \<equiv> case endpoint of RecvEP q  \<Rightarrow> Some q | _ \<Rightarrow> None"

lemma ep_of_simps:
  "ep_of (SchedContext sc n) = None"
  "ep_of (CNode n cnode) = None"
  "ep_of (TCB tcb) = None"
  "ep_of (Endpoint endpoint) = Some endpoint"
  "ep_of (Notification ntfn) = None"
  "ep_of (Reply reply) = None"
  "ep_of (ArchObj aobj) = None"
  "send_q_of IdleEP = None"
  "send_q_of (SendEP q) = Some q"
  "send_q_of (RecvEP q) = None"
  "recv_q_of IdleEP = None"
  "recv_q_of (SendEP q) = None"
  "recv_q_of (RecvEP q) = Some q"
  by (auto simp: ep_of_def send_q_of_def recv_q_of_def)

lemma ep_of_Some:
  "ep_of ko = Some ep \<longleftrightarrow> ko = Endpoint ep"
  by (simp add: ep_of_def split: kernel_object.splits)

lemma ep_of_None:
  "ep_of ko = None \<longleftrightarrow> (\<forall>ep. ko \<noteq> Endpoint ep)"
  by (simp add: ep_of_def split: kernel_object.splits)

lemma send_q_of_Some:
  "send_q_of ep = Some q \<longleftrightarrow> ep = SendEP q"
  by (simp add: send_q_of_def split: endpoint.splits)

lemma send_q_of_None:
  "send_q_of ep = None \<longleftrightarrow> (\<forall>q. ep \<noteq> SendEP q)"
  by (simp add: send_q_of_def split: endpoint.splits)

lemma recv_q_of_Some:
  "recv_q_of ep = Some q \<longleftrightarrow> ep = RecvEP q"
  by (simp add: recv_q_of_def split: endpoint.splits)

lemma recv_q_of_None:
  "recv_q_of ep = None \<longleftrightarrow> (\<forall>q. ep \<noteq> RecvEP q)"
  by (simp add: recv_q_of_def split: endpoint.splits)

definition eps_of_kh :: "('obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> 'obj_ref \<rightharpoonup> endpoint" where
  "eps_of_kh kh \<equiv> kh |> ep_of"

abbreviation eps_of :: "'z state \<Rightarrow> obj_ref \<rightharpoonup> endpoint" where
  "eps_of s \<equiv> eps_of_kh (kheap s)"

lemmas eps_of_def = eps_of_kh_def[of "kheap s" for s :: "'z state"]

global_interpretation ep_heap: opt_map_cons_def_locale _ ep_of eps_of_kh Endpoint
  using eps_of_kh_def ep_of_None ep_of_Some by unfold_locales

\<comment> \<open>Project endpoint queues\<close>

definition ep_send_qs_of_eps :: "('obj_ref \<rightharpoonup> endpoint) \<Rightarrow> 'obj_ref \<rightharpoonup> obj_ref list" where
  "ep_send_qs_of_eps eps \<equiv> eps |> send_q_of"

definition ep_recv_qs_of_eps :: "('obj_ref \<rightharpoonup> endpoint) \<Rightarrow> 'obj_ref \<rightharpoonup> obj_ref list" where
  "ep_recv_qs_of_eps eps \<equiv> eps |> recv_q_of"

abbreviation "ep_send_qs_of_kh kh \<equiv> ep_send_qs_of_eps (eps_of_kh kh)"
abbreviation "ep_send_qs_of s \<equiv> ep_send_qs_of_kh (kheap s)"

abbreviation "ep_recv_qs_of_kh kh \<equiv> ep_recv_qs_of_eps (eps_of_kh kh)"
abbreviation "ep_recv_qs_of s \<equiv> ep_recv_qs_of_kh (kheap s)"

global_interpretation ep_send_qs:  opt_map_opt_map_cons_def_locale _ ep_of eps_of_kh Endpoint send_q_of SendEP ep_send_qs_of_eps
  using ep_send_qs_of_eps_def send_q_of_None send_q_of_Some by unfold_locales

global_interpretation ep_recv_qs:
  opt_map_opt_map_cons_def_locale _ ep_of eps_of_kh Endpoint recv_q_of RecvEP ep_recv_qs_of_eps
  using ep_recv_qs_of_eps_def recv_q_of_None recv_q_of_Some by unfold_locales

\<comment> \<open>Heap simplification rules\<close>

lemmas vs_pred_map_simps =
  pred_tcb_scps_of_kh_simps
  tcb_heap.pred_map_simps
  tcb_sts.pred_map_simps
  tcb_scps.pred_map_simps
  tcb_faults.pred_map_simps
  etcbs.pred_map_simps
  sc_heap.pred_map_simps
  sc_refill_cfgs.pred_map_simps
  sc_tcbs.pred_map_simps
  sc_replies.pred_map_simps
  ep_heap.pred_map_simps
  ep_send_qs.pred_map_simps
  ep_recv_qs.pred_map_simps
  tcb_heap.pred_map_upds
  tcb_sts.pred_map_upds
  tcb_scps.pred_map_upds
  tcb_faults.pred_map_upds
  etcbs.pred_map_upds
  sc_heap.pred_map_upds
  sc_refill_cfgs.pred_map_upds
  sc_tcbs.pred_map_upds
  sc_replies.pred_map_upds
  ep_heap.pred_map_upds
  ep_send_qs.pred_map_upds
  ep_recv_qs.pred_map_upds
  pred_map_eq[where m="kheap s" for s :: "'z state"]
  pred_map_def[where m="kheap s" for s :: "'z state"]

lemmas vs_heap_simps =
  tcb_of_simps
  sc_of_simps
  ep_of_simps
  tcb_heap.simps
  tcb_sts.simps
  tcb_scps.simps
  tcb_faults.simps
  etcbs.simps
  sc_heap.simps
  sc_refill_cfgs.simps
  sc_tcbs.simps
  sc_replies.simps
  ep_heap.simps
  ep_send_qs.simps
  ep_recv_qs.simps

lemmas vs_proj_defs =
  tcb_heap.proj_def
  tcb_sts.proj_def
  tcb_scps.proj_def
  tcb_faults.proj_def
  etcbs.proj_def
  sc_heap.proj_def
  sc_refill_cfgs.proj_def
  sc_tcbs.proj_def
  sc_replies.proj_def
  ep_heap.proj_def
  ep_send_qs.proj_def
  ep_recv_qs.proj_def

lemmas vs_proj_defsym = vs_proj_defs[symmetric]

lemmas vs_upds =
  tcb_sts.upd
  tcb_scps.upd
  tcb_faults.upd
  etcbs.upd
  sc_refill_cfgs.upd
  sc_tcbs.upd
  sc_replies.upd
  ep_send_qs.upd
  ep_recv_qs.upd

lemmas vs_upd_idems =
  tcb_sts.upd_idem
  tcb_scps.upd_idem
  tcb_faults.upd_idem
  etcbs.upd_idem
  sc_refill_cfgs.upd_idem
  sc_tcbs.upd_idem
  sc_replies.upd_idem
  ep_send_qs.upd_idem
  ep_recv_qs.upd_idem

lemmas vs_all_heap_simps = vs_pred_map_simps vs_upds vs_heap_simps vs_upd_idems

\<comment> \<open>Conversions from obj_at to predicates over heap projections.
    Most often, we use these in the forwards direction, but we sometimes use then
    in reverse.\<close>

named_theorems obj_at_kh_kheap_simps

lemma get_tcb_simp[obj_at_kh_kheap_simps]:
  "get_tcb t s = tcbs_of s t"
  by (rule sym, clarsimp simp: get_tcb_def vs_heap_simps split: option.splits kernel_object.splits)

\<comment> \<open>Does not fire reliably in the forwards direction, due the presence of the obj_at
    rule below, but is sometimes needed in the reverse direction.\<close>
lemma ko_at_kh_simp[obj_at_kh_kheap_simps]:
  "ko_at ko ref s = pred_map_eq ko (kheap s) ref"
  by (simp add: obj_at_def pred_map_eq_def pred_map_def)

lemma obj_at_kh_simp[obj_at_kh_kheap_simps]:
  "obj_at P ref s = pred_map P (kheap s) ref"
  by (simp add: obj_at_def pred_map_def)

\<comment> \<open>Conversions from pred_tcb_at\<close>

lemma pred_tcb_at_kh_simp:
  "pred_tcb_at proj P t s = pred_map P (map_project (proj \<circ> tcb_to_itcb) (tcbs_of s)) t"
  by (auto simp: pred_map_map_project vs_heap_simps pred_tcb_at_def obj_at_def)

\<comment> \<open>Does not fire reliably in the forwards direction, due the presence of the pred_tcb_at
    rule above, but is sometimes needed in the reverse direction.\<close>
lemma pred_tcb_at_kh_eq_simp:
  "pred_tcb_at proj ((=) v) t s = pred_map_eq v (map_project (proj \<circ> tcb_to_itcb) (tcbs_of s)) t"
  by (auto simp: pred_map_eq_normalise pred_tcb_at_kh_simp)

lemmas pred_tcb_at_kh_simps = pred_tcb_at_kh_eq_simp pred_tcb_at_kh_simp

context
  notes tcb_at_kh_simps' =
    pred_tcb_at_kh_simps[of itcb_state]
    pred_tcb_at_kh_simps[of itcb_sched_context]
    pred_tcb_at_kh_simps[of itcb_fault]
begin
  lemmas tcb_at_kh_simps[obj_at_kh_kheap_simps] =
    tcb_at_kh_simps'[simplified comp_def, simplified, folded vs_proj_defs]
end

\<comment> \<open>Conversions from sc_at_ppred\<close>

lemma sc_at_ppred_kh_simp:
  "sc_at_ppred proj P scp s = pred_map P (map_project proj (scs_of s)) scp"
  by (auto simp: pred_map_map_project vs_heap_simps sc_at_ppred_def obj_at_def)

lemma sc_at_ppred_kh_eq_simp:
  "sc_at_ppred proj ((=) v) scp s = pred_map_eq v (map_project proj (scs_of s)) scp"
  by (auto simp: sc_at_ppred_kh_simp pred_map_eq_normalise)

lemmas sc_at_ppred_kh_simps = sc_at_ppred_kh_simp sc_at_ppred_kh_eq_simp

lemma sc_at_ppred_to_pred_map_sc_refill_cfgs_of:
  assumes "\<And>sc. scrc_f (sc_refill_cfg_of sc) = sc_f sc"
  shows "sc_at_ppred sc_f P scp s = pred_map (\<lambda>rc. P (scrc_f rc)) (sc_refill_cfgs_of s) scp"
  by (auto simp: sc_at_ppred_def obj_at_def vs_all_heap_simps assms)

context
  notes sc_at_kh_simps' =
    sc_at_ppred_kh_simps[of sc_refill_cfg_of]
    sc_at_ppred_kh_simps[of sc_tcb]
    sc_at_ppred_kh_simps[of sc_replies]
  notes sc_at_kh_simps'' =
    sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f=scrc_refills and sc_f=sc_refills]
    sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f=scrc_refill_max and sc_f=sc_refill_max]
    sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f=scrc_period and sc_f=sc_period]
    sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f=scrc_budget and sc_f=sc_budget]
begin
  lemmas sc_at_kh_simps[obj_at_kh_kheap_simps] =
    sc_at_kh_simps'[simplified, folded vs_proj_defs]
    sc_at_kh_simps''[simplified]
end

\<comment> \<open>Some weaker consequences of sym_refs that are sometimes easier to push through proofs\<close>

abbreviation heap_ref_eq :: "'a \<Rightarrow> 'b \<Rightarrow> ('b \<rightharpoonup> 'a option) \<Rightarrow> bool" where
  "heap_ref_eq r p heap \<equiv> pred_map_eq (Some r) heap p"

definition heap_refs_retract_at :: "('a \<rightharpoonup> 'b option) \<Rightarrow> ('b \<rightharpoonup> 'a option) \<Rightarrow> 'a \<Rightarrow> bool" where
  "heap_refs_retract_at heap symheap p \<equiv> \<forall>r. heap_ref_eq r p heap \<longrightarrow> heap_ref_eq p r symheap"

definition heap_refs_retract :: "('a \<rightharpoonup> 'b option) \<Rightarrow> ('b \<rightharpoonup> 'a option) \<Rightarrow> bool" where
  "heap_refs_retract heap symheap \<equiv> \<forall>p. heap_refs_retract_at heap symheap p"

definition heap_refs_inv :: "('a \<rightharpoonup> 'b option) \<Rightarrow> ('b \<rightharpoonup> 'a option) \<Rightarrow> bool" where
  "heap_refs_inv heap symheap \<equiv> heap_refs_retract heap symheap \<and> heap_refs_retract symheap heap"

lemmas heap_refs_inv_defs = heap_refs_inv_def heap_refs_retract_def heap_refs_retract_at_def

lemma heap_refs_inv_def2:
  "heap_refs_inv heap symheap \<equiv> \<forall>p q. heap_ref_eq q p heap \<longleftrightarrow> heap_ref_eq p q symheap"
  by (auto simp: atomize_eq heap_refs_inv_defs)

definition heap_refs_inj_at_ref :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b option) \<Rightarrow> bool" where
  "heap_refs_inj_at_ref p ref heap \<equiv> \<forall>p'. heap_ref_eq ref p' heap \<longrightarrow> p' = p"

definition heap_refs_inj_at :: "'a \<Rightarrow> ('a \<rightharpoonup> 'b option) \<Rightarrow> bool" where
  "heap_refs_inj_at p heap \<equiv> \<forall>ref. heap_ref_eq ref p heap \<longrightarrow> heap_refs_inj_at_ref p ref heap"

definition heap_refs_inj :: "('a \<rightharpoonup> 'b option) \<Rightarrow> bool" where
  "heap_refs_inj heap \<equiv> \<forall>p. heap_refs_inj_at p heap"

lemmas heap_ref_inj_defs = heap_refs_inj_def heap_refs_inj_at_def heap_refs_inj_at_ref_def

lemma heap_refs_retract_atD:
  assumes "heap_refs_retract_at heap symheap p"
  assumes "heap_ref_eq r p heap"
  shows "heap_ref_eq p r symheap"
  using assms by (auto simp: heap_refs_retract_at_def)

lemma heap_refs_retract_heap_refs_retract_at[simp, elim!]:
  "heap_refs_retract heap symheap \<Longrightarrow> heap_refs_retract_at heap symheap p"
  by (auto simp: heap_refs_retract_def)

lemmas heap_refs_retractD = heap_refs_retract_atD[OF heap_refs_retract_heap_refs_retract_at]

lemma heap_refs_retractE:
  assumes "heap_refs_retract heap symheap"
  assumes "\<And>p r. heap_ref_eq r p heap'
                  \<longrightarrow> (heap_ref_eq r p heap \<longrightarrow> heap_ref_eq p r symheap)
                  \<longrightarrow> heap_ref_eq p r sym_heap'"
  shows "heap_refs_retract heap' sym_heap'"
  using assms by (simp add: heap_refs_inv_defs)

lemma heap_refs_inv_retractD:
  "heap_refs_inv heap symheap \<Longrightarrow> heap_refs_retract heap symheap"
  by (simp add: heap_refs_inv_def)

lemma heap_refs_inv_retract_symD:
  "heap_refs_inv heap symheap \<Longrightarrow> heap_refs_retract symheap heap"
  by (simp add: heap_refs_inv_def)

lemma heap_refs_inv_inv:
  "heap_refs_inv heap symheap \<Longrightarrow> heap_refs_inv symheap heap"
  by (simp add: heap_refs_inv_def)

lemma heap_refs_retract_heap_ref_inj:
  assumes "heap_refs_retract heap symheap"
  shows "heap_refs_inj heap"
  using assms
  apply (clarsimp simp: heap_ref_inj_defs)
  apply (frule_tac p=p in heap_refs_retractD, assumption)
  apply (frule_tac p=p' in heap_refs_retractD, assumption)
  by (clarsimp simp: pred_map_simps)

lemma heap_refs_inj_for_ref_resolve:
  assumes "heap_ref_eq ref p heap"
  shows "heap_refs_inj_at p heap \<longleftrightarrow> heap_refs_inj_at_ref p ref heap"
  using assms by (simp add: heap_refs_inj_at_def pred_map_simps)

lemma heap_refs_injD:
  "heap_refs_inj heap \<Longrightarrow> heap_refs_inj_at p heap"
  by (simp add: heap_refs_inj_def)

lemma heap_refs_inj_at_eq:
  "heap_refs_inj_at p heap
   \<Longrightarrow> heap_ref_eq r p heap
   \<Longrightarrow> heap_ref_eq r p' heap
   \<Longrightarrow> p' = p"
  by (clarsimp simp: heap_refs_inj_for_ref_resolve heap_refs_inj_at_ref_def)

lemmas heap_refs_inj_eq = heap_refs_inj_at_eq[OF heap_refs_injD]
lemmas heap_refs_retract_inj_eq = heap_refs_inj_eq[OF heap_refs_retract_heap_ref_inj]

lemma heap_refs_retract_at_eq:
  "heap_refs_retract_at heap symheap p
   \<Longrightarrow> heap_ref_eq r p heap
   \<Longrightarrow> heap_ref_eq p' r symheap
   \<Longrightarrow> p' = p"
  by (auto simp: pred_map_simps dest!: heap_refs_retract_atD)

lemmas heap_refs_retract_eq = heap_refs_retract_at_eq[OF heap_refs_retract_heap_refs_retract_at]

lemma heap_refs_inj_at_prop:
  assumes inj: "heap_refs_inj_at p heap"
  assumes eq: "heap_ref_eq r p heap"
  shows "(\<forall>p'. heap_ref_eq r p' heap \<longrightarrow> P p') = P p"
  using inj[unfolded heap_refs_inj_for_ref_resolve[OF eq], unfolded heap_refs_inj_at_ref_def]
  by (auto simp: eq)

lemmas heap_refs_inj_prop = heap_refs_inj_at_prop[OF heap_refs_injD]

lemma sym_refs_retract_sc_tcbs[simp, elim!]:
  "sym_refs (state_refs_of s) \<Longrightarrow> heap_refs_retract (sc_tcbs_of s) (tcb_scps_of s)"
  apply (clarsimp simp: heap_refs_inv_defs)
  by (frule_tac x=p and y=r and tp=TCBSchedContext in sym_refsE
      ; clarsimp simp: in_state_refs_of_iff refs_of_rev vs_all_heap_simps)

lemma sym_refs_retract_tcb_scps[simp, elim!]:
  "sym_refs (state_refs_of s) \<Longrightarrow> heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)"
  apply (clarsimp simp: heap_refs_inv_defs)
  by (frule_tac x=p and y=r and tp=SCTcb in sym_refsE
      ; clarsimp simp: in_state_refs_of_iff refs_of_rev vs_all_heap_simps)

lemma sym_refs_inv_tcb_scps[simp, elim!]:
  "sym_refs (state_refs_of s) \<Longrightarrow> heap_refs_inv (tcb_scps_of s) (sc_tcbs_of s)"
  by (simp add: heap_refs_inv_def)

lemma sym_refs_inv_sc_tcbs[simp, elim!]:
  "sym_refs (state_refs_of s) \<Longrightarrow> heap_refs_inv (sc_tcbs_of s) (tcb_scps_of s)"
  by (simp add: heap_refs_inv_def)

(* FIXME RT: generate these with a locale *)
lemmas invs_retract_tcb_scps[simp, elim!] = sym_refs_retract_tcb_scps[OF invs_sym_refs]
lemmas invs_retract_sc_tcbs[simp, elim!] = sym_refs_retract_sc_tcbs[OF invs_sym_refs]
lemmas invs_heap_refs_inv_tcb_scps[simp, elim!] = sym_refs_inv_tcb_scps[OF invs_sym_refs]
lemmas invs_heap_refs_inv_sc_tcbs[simp, elim!] = sym_refs_inv_sc_tcbs[OF invs_sym_refs]
lemmas sym_refs_inj_tcb_scps = sym_refs_retract_tcb_scps[THEN heap_refs_retract_heap_ref_inj]
lemmas sym_refs_inj_sc_tcbs = sym_refs_retract_sc_tcbs[THEN heap_refs_retract_heap_ref_inj]
lemmas invs_inj_tcb_scps = sym_refs_inj_tcb_scps[OF invs_sym_refs]
lemmas invs_inj_sc_tcbs = sym_refs_inj_sc_tcbs[OF invs_sym_refs]

\<comment> \<open>Lifting rules for generic heap projections\<close>

lemma pred_map_heap_lift:
  assumes "\<And>N P x. \<lbrace>\<lambda>s. N (pred_map P (heap s) x) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_map P (heap s) x)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (heap s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (heap s)\<rbrace>"
  apply (clarsimp simp: valid_def elim!: ssubst[rotated, of P] intro!: pred_map_map_eqI)
  by (erule use_valid[OF _ assms]; simp)

lemma pred_map_heap_lower:
  assumes "\<And>P. \<lbrace>\<lambda>s. P (heap s ref) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (heap s ref) \<rbrace>"
  shows "\<lbrace>\<lambda>s. N (pred_map P (heap s) ref) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_map P (heap s) ref)\<rbrace>"
  apply (rule validI, clarsimp)
  apply (rule bool_to_bool_cases[of N]; simp; thin_tac "N = _")
   apply ((drule use_valid, rule_tac P="\<lambda>x. \<exists>y. x = Some y \<and> P y" in assms)
          ; clarsimp simp: pred_map_simps)
  apply ((drule use_valid, rule_tac P="\<lambda>x. \<forall>y. x = Some y \<longrightarrow> \<not> P y" in assms)
         ; clarsimp simp: pred_map_simps)
  done

lemma pred_map2_lift_strong':
  assumes "\<And>P. \<lbrace>\<lambda>s. P (g s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (g s)\<rbrace>"
  assumes "\<And>x. \<lbrace>\<lambda>s. N (\<exists>p. pred_map_eq p (heap s) t \<and> pred_map (P x) (heap' s) p) \<and> R s\<rbrace>
                f \<lbrace>\<lambda>rv s. N (\<exists>p. pred_map_eq p (heap s) t \<and> pred_map (P x) (heap' s) p)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (pred_map2 (P (g s)) (heap s) (heap' s) t) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rv s. N (pred_map2 (P (g s)) (heap s) (heap' s) t)\<rbrace>"
  by (clarsimp simp: pred_map2_pred_maps
             intro!: hoare_lift_concrete_Pf_pre_conj[where f=g, OF assms])

lemmas pred_map2_lift_strong =
  pred_map2_lift_strong'[where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF hoare_vcg_prop_pre_conj]

lemma pred_map_eq_lift:
  assumes tcb: "\<And>P. \<lbrace>\<lambda>s. N (pred_map P (heap s) t) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_map P (heap s) t)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (pred_map_eq obj (heap s) t) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_map_eq obj (heap s) t)\<rbrace>"
  unfolding pred_map_eq_def by (rule tcb)

lemma pred_map2_lift':
  assumes g: "\<And>P. \<lbrace>\<lambda>s. P (g s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (g s)\<rbrace>"
  assumes tcb: "\<And>P. \<lbrace>\<lambda>s. N (pred_map P (heap s) t) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_map P (heap s) t)\<rbrace>"
  assumes sc: "\<And>x p. \<lbrace>\<lambda>s. N (pred_map (P x) (heap' s) p) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_map (P x) (heap' s) p)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (pred_map2 (P (g s)) (heap s) (heap' s) t) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rv s. N (pred_map2 (P (g s)) (heap s) (heap' s) t)\<rbrace>"
  by (intro pred_map2_lift_strong'[where g=g and P=P, OF g] pred_map_eq_lift tcb sc
            hoare_vcg_ex_lift_N_pre_conj hoare_vcg_conj_lift_N_pre_conj)

lemmas pred_map2_lift =
  pred_map2_lift'[where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF hoare_vcg_prop_pre_conj]

lemma map_join_lift:
  assumes "\<And>N ref obj. \<lbrace>\<lambda>s. N (heap s ref = Some (Some obj)) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (heap s ref = Some (Some obj))\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (map_join (heap s)) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (map_join (heap s))\<rbrace>"
  apply (rule validI; elim conjE rsubst[of N]; intro map_eqI iffI; rule ccontr; clarsimp simp: map_join_simps; rename_tac ref obj)
     apply (frule use_valid, rule_tac N=Not and ref=ref and obj=obj in assms; clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
    apply (frule use_valid, rule_tac N=id and ref=ref and obj=obj in assms; clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
   apply (frule use_valid, rule_tac N=id and ref=ref and obj=obj in assms; clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  apply (frule use_valid, rule_tac N=Not and ref=ref and obj=obj in assms; clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
  done

\<comment> \<open>Lifting rules for specific heap projections.\<close>

lemmas sc_at_pred_n_lift_s =
  hoare_lift_Pf[where P="\<lambda>f s. M (sc_at_pred_n N proj (P f) p s)" for M N proj P p]

lemmas sc_at_ppred_lift_s = sc_at_pred_n_lift_s[where N=\<top>]

lemma pred_tcb_proj_lift:
  assumes "\<lbrace>\<lambda>s. N (pred_tcb_at proj P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_tcb_at proj P t s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (pred_map P (map_project (proj \<circ> tcb_to_itcb) (tcbs_of s)) t) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rv s. N (pred_map P (map_project (proj \<circ> tcb_to_itcb) (tcbs_of s)) t)\<rbrace>"
  by (rule assms[unfolded pred_tcb_at_kh_simp])

lemmas pred_tcb_st_lift =
  pred_tcb_proj_lift[where proj=itcb_state, simplified comp_def, simplified, folded vs_proj_defs]
lemmas pred_tcb_scp_lift =
  pred_tcb_proj_lift[where proj=itcb_sched_context, simplified comp_def, simplified, folded vs_proj_defs]
lemmas pred_tcb_fault_lift =
  pred_tcb_proj_lift[where proj=itcb_fault, simplified comp_def, simplified, folded vs_proj_defs]

lemma pred_tcb_proj_lower:
  assumes "\<lbrace>\<lambda>s. N (pred_map P (map_project (proj \<circ> tcb_to_itcb) (tcbs_of s)) t) \<and> R s\<rbrace>
            f \<lbrace>\<lambda>rv s. N (pred_map P (map_project (proj \<circ> tcb_to_itcb) (tcbs_of s)) t)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (pred_tcb_at proj P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_tcb_at proj P t s)\<rbrace>"
  unfolding pred_tcb_at_kh_simp by (rule assms)

lemmas pred_tcb_st_lower =
  pred_tcb_proj_lower[where proj=itcb_state, simplified comp_def, simplified, folded vs_proj_defs]
lemmas pred_tcb_scp_lower =
  pred_tcb_proj_lower[where proj=itcb_sched_context, simplified comp_def, simplified, folded vs_proj_defs]
lemmas pred_tcb_fault_lower =
  pred_tcb_proj_lower[where proj=itcb_fault, simplified comp_def, simplified, folded vs_proj_defs]

lemma pred_sc_proj_lift:
  assumes "\<lbrace>\<lambda>s. N (sc_at_ppred proj P scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_at_ppred proj P scp s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (pred_map P (map_project proj (scs_of s)) scp) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rv s. N (pred_map P (map_project proj (scs_of s)) scp)\<rbrace>"
  by (rule assms[unfolded sc_at_ppred_kh_simp])

lemma pred_sc_refill_cfg_proj_lift:
  assumes f: "\<And>sc. scrc_f (sc_refill_cfg_of sc) = sc_f sc"
  assumes p: "\<lbrace>\<lambda>s. N (sc_at_ppred sc_f P scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_at_ppred sc_f P scp s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (pred_map (\<lambda>rc. P (scrc_f rc)) (sc_refill_cfgs_of s) scp) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rv s. N (pred_map (\<lambda>rc. P (scrc_f rc)) (sc_refill_cfgs_of s) scp)\<rbrace>"
  by (simp add: p[unfolded sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f=scrc_f, OF f]])

lemmas pred_sc_proj_lifts =
  pred_sc_proj_lift[where proj=sc_replies, folded vs_proj_defs]
  pred_sc_refill_cfg_proj_lift[where scrc_f=scrc_refills and sc_f=sc_refills, simplified]
  pred_sc_refill_cfg_proj_lift[where scrc_f=scrc_refill_max and sc_f=sc_refill_max, simplified]
  pred_sc_refill_cfg_proj_lift[where scrc_f=scrc_period and sc_f=sc_period, simplified]
  pred_sc_refill_cfg_proj_lift[where scrc_f=id and sc_f=sc_refill_cfg_of, simplified]

lemma pred_sc_proj_lower:
  assumes "\<lbrace>\<lambda>s. N (pred_map P (map_project proj (scs_of s)) scp) \<and> R s\<rbrace>
           f \<lbrace>\<lambda>rv s. N (pred_map P (map_project proj (scs_of s)) scp)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (sc_at_ppred proj P scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_at_ppred proj P scp s)\<rbrace>"
  unfolding sc_at_ppred_kh_simp by (rule assms)

lemma pred_sc_refill_cfg_proj_lower:
  assumes f: "\<And>sc. scrc_f (sc_refill_cfg_of sc) = sc_f sc"
  assumes p: "\<lbrace>\<lambda>s. N (pred_map (\<lambda>rc. P (scrc_f rc)) (sc_refill_cfgs_of s) scp) \<and> R s\<rbrace>
              f \<lbrace>\<lambda>rv s. N (pred_map (\<lambda>rc. P (scrc_f rc)) (sc_refill_cfgs_of s) scp)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (sc_at_ppred sc_f P scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_at_ppred sc_f P scp s)\<rbrace>"
  unfolding sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f=scrc_f, OF f] by (rule p)

lemmas pred_sc_proj_lowers =
  pred_sc_proj_lower[where proj=sc_replies, folded vs_proj_defs]
  pred_sc_refill_cfg_proj_lower[where scrc_f=scrc_refills and sc_f=sc_refills, simplified]
  pred_sc_refill_cfg_proj_lower[where scrc_f=scrc_refill_max and sc_f=sc_refill_max, simplified]
  pred_sc_refill_cfg_proj_lower[where scrc_f=scrc_period and sc_f=sc_period, simplified]
  pred_sc_refill_cfg_proj_lower[where scrc_f=id and sc_f=sc_refill_cfg_of, simplified]

lemmas valid_sched_pred_heap_proj_lifts =
  pred_tcb_st_lift pred_tcb_scp_lift pred_tcb_fault_lift
  pred_sc_proj_lifts

lemmas valid_sched_pred_heap_proj_lowers =
  pred_tcb_st_lower pred_tcb_scp_lower pred_tcb_fault_lower
  pred_sc_proj_lowers

lemma proj_tcbs_of_lift:
  assumes "\<And>N P t. \<lbrace>\<lambda>s. N (pred_tcb_at proj P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_tcb_at proj P t s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (map_project (proj \<circ> tcb_to_itcb) (tcbs_of s)) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rv s. P (map_project (proj \<circ> tcb_to_itcb) (tcbs_of s))\<rbrace>"
  apply (rule validI; elim conjE rsubst[of P])
  apply (rule map_eqI; rule iffI; rule ccontr; clarsimp simp: map_project_simps vs_heap_simps; rename_tac t tcb)
     apply (frule use_valid, rule_tac N=Not and P=\<top> and t=t in assms; clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
    apply (frule use_valid, rule_tac N=id and P=\<top> and t=t in assms; clarsimp simp: pred_tcb_at_def obj_at_def is_tcb)
   apply (frule use_valid, rule_tac N=id and P="\<lambda>st. st = proj (tcb_to_itcb tcb)" and t=t in assms; clarsimp simp: pred_tcb_at_def obj_at_def)
  apply (frule use_valid, rule_tac N=Not and P="\<lambda>st. st = proj (tcb_to_itcb tcb)" and t=t in assms; clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemmas tcb_sts_of_lift =
  proj_tcbs_of_lift[where proj=itcb_state, simplified comp_def, simplified, folded vs_proj_defs]
lemmas tcb_scps_of_lift =
  proj_tcbs_of_lift[where proj=itcb_sched_context, simplified comp_def, simplified, folded vs_proj_defs]
lemmas tcb_faults_of_lift =
  proj_tcbs_of_lift[where proj=itcb_fault, simplified comp_def, simplified, folded vs_proj_defs]

lemma proj_scs_of_lift:
  assumes "\<And>N P scp. \<lbrace>\<lambda>s. N (sc_at_ppred proj P scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_at_ppred proj P scp s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (map_project proj (scs_of s)) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (map_project proj (scs_of s))\<rbrace>"
  apply (rule validI; elim conjE rsubst[of P])
  apply (rule map_eqI; rule iffI; rule ccontr; clarsimp simp: map_project_simps vs_heap_simps; rename_tac scp sc n)
     apply (frule use_valid, rule_tac N=Not and P=\<top> and scp=scp in assms; clarsimp simp: sc_at_ppred_def obj_at_def)
    apply (frule use_valid, rule_tac N=id and P=\<top> and scp=scp in assms; clarsimp simp: sc_at_ppred_def obj_at_def)
   apply (frule use_valid, rule_tac N=id and P="\<lambda>scpo. scpo = proj sc" and scp=scp in assms; clarsimp simp: sc_at_ppred_def obj_at_def)
  apply (frule use_valid, rule_tac N=Not and P="\<lambda>scpo. scpo = proj sc" and scp=scp in assms; clarsimp simp: sc_at_ppred_def obj_at_def)
  done

lemmas sc_refill_cfgs_of_lift =
  proj_scs_of_lift[where proj=sc_refill_cfg_of, folded vs_proj_defs]

lemmas sc_replies_of_lift =
  proj_scs_of_lift[where proj=sc_replies, folded vs_proj_defs]

lemmas valid_sched_heap_proj_lifts =
  tcb_sts_of_lift tcb_scps_of_lift tcb_faults_of_lift
  sc_refill_cfgs_of_lift sc_replies_of_lift

\<comment> \<open>Schedulability condition: sc_refill_max must be positive\<close>

abbreviation active_scrc :: "sc_refill_cfg \<Rightarrow> bool" where
  "active_scrc cfg \<equiv> active_sc (scrc_refill_max cfg)"

lemmas active_scrc_def = active_sc_def

lemma is_sc_active_kh_simp[obj_at_kh_kheap_simps]:
  "is_sc_active scp s = pred_map active_scrc (sc_refill_cfgs_of s) scp"
  by (auto simp: is_sc_active_def vs_all_heap_simps
          split: option.splits kernel_object.splits)

abbreviation is_active_sc :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "is_active_sc scp s \<equiv> pred_map active_scrc (sc_refill_cfgs_of s) scp"

lemmas is_active_sc_def =
  sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f=scrc_refill_max
                                              and sc_f=sc_refill_max
                                              and P="active_sc"
                                            , simplified, symmetric]

\<comment> \<open>Schedulability condition: head of sc_refills must have sufficient budget for usage\<close>

abbreviation refill_sufficient_sc :: "time \<Rightarrow> sc_refill_cfg \<Rightarrow> bool" where
  "refill_sufficient_sc usage cfg \<equiv> refill_sufficient usage (scrc_refill_hd cfg)"

lemmas refill_sufficient_sc_def
  = refill_sufficient_def[where refill="scrc_refill_hd cfg" for cfg :: sc_refill_cfg]

abbreviation is_refill_sufficient :: "time \<Rightarrow> obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "is_refill_sufficient usage scp s \<equiv> pred_map (refill_sufficient_sc usage) (sc_refill_cfgs_of s) scp"

lemmas is_refill_sufficient_def =
  sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f="scrc_refill_hd"
                                              and sc_f="refill_hd"
                                              and P="refill_sufficient usage"
                                              for usage
                                            , simplified, symmetric]

\<comment> \<open>Schedulability condition: head of sc_refills must not be too far in the future\<close>

abbreviation refill_ready_sc :: "time \<Rightarrow> sc_refill_cfg \<Rightarrow> bool" where
  "refill_ready_sc curtime cfg \<equiv> refill_ready curtime (scrc_refill_hd cfg)"

lemmas refill_ready_sc_def
  = refill_ready_def[where refill="scrc_refill_hd cfg" for cfg :: sc_refill_cfg]

abbreviation is_refill_ready :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "is_refill_ready scp s \<equiv> pred_map (refill_ready_sc (cur_time s)) (sc_refill_cfgs_of s) scp"

lemmas is_refill_ready_def =
  sc_at_ppred_to_pred_map_sc_refill_cfgs_of[where scrc_f=scrc_refill_hd
                                              and sc_f=refill_hd
                                              and P="refill_ready (cur_time s)"
                                              and s=s for s
                                            , simplified, symmetric]

lemmas is_refill_ready_lift =
  sc_at_ppred_lift_s[where proj=refill_hd and P=refill_ready and f=cur_time]

definition
  window :: "refill list \<Rightarrow> ticks \<Rightarrow> bool"
where
  "window refills period \<equiv> unat (r_time (last refills)) \<le> unat (r_time (hd refills)) + unat period"

definition rr_valid_refills :: "refill list \<Rightarrow> nat \<Rightarrow> ticks \<Rightarrow> bool" where
  "rr_valid_refills refills refill_max budget \<equiv>
     (refills_sum refills = budget
      \<and> (MIN_BUDGET \<le> r_amount (hd refills))
      \<and> (unat (r_amount (hd refills)) + unat (r_amount (last refills)) \<le> unat max_time)
      \<and> length refills = 2
      \<and> MIN_BUDGET \<le> budget
      \<and> refill_max = MIN_REFILLS
      \<and> budget \<le> MAX_PERIOD)"

definition sp_valid_refills :: "refill list \<Rightarrow> nat \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> bool" where
  "sp_valid_refills refills refill_max period budget \<equiv>
      (refills_sum refills = budget
      \<and> ordered_disjoint refills
      \<and> no_overflow refills
      \<and> window refills period
      \<and> MIN_BUDGET \<le> r_amount (hd refills)
      \<and> 0 < length refills
      \<and> length refills \<le> refill_max
      \<and> MIN_BUDGET \<le> budget
      \<and> budget \<le> period
      \<and> MIN_REFILLS \<le> refill_max
      \<and> period \<le> MAX_PERIOD)"

\<comment> \<open>unat is monotonic on le\<close>
lemma unat_le_mono:
  "a \<le> b \<Longrightarrow> unat a \<le> unat b"
  by (clarsimp simp: word_le_nat_alt)

\<comment> \<open>unat is bounded above by unat max_word\<close>
(* FIXME RT: move *)
lemmas unat_bounded_above[simp] = unat_le_mono[OF max_word_max]

definition
  round_robin :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool"
where
  "round_robin sc_ptr s \<equiv> pred_map (\<lambda>cfg. scrc_period cfg = 0) (sc_refill_cfgs_of s) sc_ptr"

\<comment>\<open>When the user creates a scheduling context with period = budget, we know that sporadic scheduling is
vastly simplified. As an optimisation we set period=0 and sc_refill_max=MIN_REFILLS and adjust the
code to handle this as a special case.\<close>
definition cfg_valid_refills :: "sc_refill_cfg \<Rightarrow> bool" where
  "cfg_valid_refills cfg \<equiv>
     if (scrc_period cfg = 0) then
       rr_valid_refills (scrc_refills cfg) (scrc_refill_max cfg) (scrc_budget cfg)
     else
       sp_valid_refills (scrc_refills cfg) (scrc_refill_max cfg) (scrc_period cfg) (scrc_budget cfg)"

abbreviation valid_refills_pred :: "(obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "valid_refills_pred \<equiv> pred_map cfg_valid_refills"
abbreviation valid_refills :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "valid_refills scp s \<equiv> valid_refills_pred (sc_refill_cfgs_of s) scp"

abbreviation sc_valid_refills :: "sched_context \<Rightarrow> bool" where
  "sc_valid_refills sc \<equiv> cfg_valid_refills (sc_refill_cfg_of sc)"

lemmas sc_valid_refills_def = cfg_valid_refills_def sp_valid_refills_def
lemmas valid_refills_def = cfg_valid_refills_def sp_valid_refills_def

\<comment> \<open>Predicates about scheduling contexts bound to threads, concerning schedulability\<close>

abbreviation active_sc_tcb_at_pred :: "(obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "active_sc_tcb_at_pred \<equiv> pred_map2' active_scrc"
abbreviation active_sc_tcb_at_kh :: "(obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "active_sc_tcb_at_kh kh \<equiv> active_sc_tcb_at_pred (tcb_scps_of_kh kh) (sc_refill_cfgs_of_kh kh)"
abbreviation active_sc_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "active_sc_tcb_at t s \<equiv> active_sc_tcb_at_pred (tcb_scps_of s) (sc_refill_cfgs_of s) t"

abbreviation budget_ready_pred :: "time \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "budget_ready_pred curtime \<equiv> pred_map2' (refill_ready_sc curtime)"
abbreviation budget_ready_kh :: "time \<Rightarrow> (obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "budget_ready_kh curtime kh \<equiv> budget_ready_pred curtime (tcb_scps_of_kh kh) (sc_refill_cfgs_of_kh kh)"
abbreviation budget_ready :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "budget_ready t s \<equiv> budget_ready_pred (cur_time s) (tcb_scps_of s) (sc_refill_cfgs_of s) t"

abbreviation budget_sufficient_pred  :: "(obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup>sc_refill_cfg) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "budget_sufficient_pred \<equiv> pred_map2' (refill_sufficient_sc 0)"
abbreviation budget_sufficient_kh :: "(obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "budget_sufficient_kh kh \<equiv> budget_sufficient_pred (tcb_scps_of_kh kh) (sc_refill_cfgs_of_kh kh)"
abbreviation budget_sufficient :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "budget_sufficient t s \<equiv> budget_sufficient_pred (tcb_scps_of s) (sc_refill_cfgs_of s) t"

\<comment> \<open>Threads with scheduling contexts that have been released: all three conditions at once\<close>
abbreviation released_sc :: "time \<Rightarrow> sc_refill_cfg \<Rightarrow> bool" where
  "released_sc curtime sc \<equiv> active_scrc sc \<and> refill_ready_sc curtime sc \<and> refill_sufficient_sc 0 sc"
abbreviation released_sc_tcb_at_pred :: "time \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "released_sc_tcb_at_pred curtime \<equiv> pred_map2' (released_sc curtime)"
abbreviation released_sc_tcb_at_kh :: "time \<Rightarrow> (obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "released_sc_tcb_at_kh curtime kh \<equiv> released_sc_tcb_at_pred curtime (tcb_scps_of_kh kh) (sc_refill_cfgs_of_kh kh)"
abbreviation released_sc_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "released_sc_tcb_at t s \<equiv> released_sc_tcb_at_pred (cur_time s) (tcb_scps_of s) (sc_refill_cfgs_of s) t"

lemma released_sc_tcb_at_def:
  "released_sc_tcb_at_pred curtime tcb_scps sc_refill_cfgs t
    \<longleftrightarrow> active_sc_tcb_at_pred tcb_scps sc_refill_cfgs t
        \<and> budget_ready_pred curtime tcb_scps sc_refill_cfgs t
        \<and> budget_sufficient_pred tcb_scps sc_refill_cfgs t"
  by (simp add: pred_map2_conj)

lemma released_sc_tcb_at_lift:
  assumes "\<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
  assumes "\<lbrace>\<lambda>s. budget_ready t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_ready t s\<rbrace>"
  assumes "\<lbrace>\<lambda>s. budget_sufficient t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_sufficient t s\<rbrace>"
  shows "\<lbrace>\<lambda>s. released_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. released_sc_tcb_at t s\<rbrace>"
  unfolding released_sc_tcb_at_def
  by (intro hoare_vcg_conj_lift_N_pre_conj[where N="\<lambda>P. P"] assms)

abbreviation released_sc_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "released_sc_at scptr s \<equiv> pred_map (released_sc (cur_time s)) (sc_refill_cfgs_of s) scptr"

lemma sc_at_pred_to_pred_map_sc_refill_cfgs_of:
  assumes "\<And>sc. P sc = P' (sc_refill_cfg_of sc)"
  shows "sc_at_pred P scp s = pred_map P' (sc_refill_cfgs_of s) scp"
  by (auto simp: sc_at_pred_def obj_at_def vs_all_heap_simps assms)

lemmas sc_at_released_kh_simps[obj_at_kh_kheap_simps] =
  sc_at_pred_to_pred_map_sc_refill_cfgs_of[where P="sc_released curtime" and P'="released_sc curtime" for curtime, simplified sc_released_def, simplified]

\<comment> \<open>Sometimes, it will be useful to work with a generalisation of all 4 of the preceding predicates\<close>
abbreviation bound_sc_obj_tcb_at_kh :: "(sc_refill_cfg \<Rightarrow> bool) \<Rightarrow> (obj_ref \<rightharpoonup> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "bound_sc_obj_tcb_at_kh P kh \<equiv> pred_map2' P (tcb_scps_of_kh kh) (sc_refill_cfgs_of_kh kh)"
abbreviation bound_sc_obj_tcb_at :: "(sc_refill_cfg \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "bound_sc_obj_tcb_at P t s \<equiv> pred_map2' P (tcb_scps_of s) (sc_refill_cfgs_of s) t"

lemma is_schedulable_opt_Some:
  "is_schedulable_opt t s = Some X \<Longrightarrow>
          st_tcb_at runnable t s \<and> active_sc_tcb_at t s \<and> \<not> (in_release_queue t s) \<longleftrightarrow> X"
  by (clarsimp simp: is_schedulable_opt_def vs_all_heap_simps obj_at_kh_kheap_simps
              split: option.splits)

lemma is_schedulable_bool_def2:
  "is_schedulable_bool t s = (st_tcb_at runnable t s \<and> active_sc_tcb_at t s
                               \<and> \<not> (in_release_queue t s))"
  by (clarsimp simp: is_schedulable_bool_def vs_all_heap_simps obj_at_kh_kheap_simps
              split: option.splits)

\<comment> \<open>Like refill_ready', but using unat addition to avoid the need to reason about overflow.\<close>
definition refill_ready_no_overflow :: "time \<Rightarrow> time \<Rightarrow> refill \<Rightarrow> bool" where
  "refill_ready_no_overflow usage curtime refill \<equiv> unat (r_time refill) + unat usage \<le> unat curtime + unat kernelWCET_ticks"

abbreviation refill_ready_no_overflow_sc :: "time \<Rightarrow> time \<Rightarrow> sc_refill_cfg \<Rightarrow> bool" where
  "refill_ready_no_overflow_sc usage curtime cfg \<equiv> refill_ready_no_overflow usage curtime (scrc_refill_hd cfg)"

abbreviation cur_sc_offset_ready :: "time \<Rightarrow> 'z state \<Rightarrow> bool" where
  "cur_sc_offset_ready usage s \<equiv> pred_map (refill_ready_no_overflow_sc usage (cur_time s)) (sc_refill_cfgs_of s) (cur_sc s)"

lemmas cur_sc_offset_ready_def = refill_ready_no_overflow_def

definition consumed_time_bounded_2 where
  "consumed_time_bounded_2 constime curtime \<equiv> (unat constime \<le> unat curtime)"

abbreviation consumed_time_bounded :: "'z::state_ext state \<Rightarrow> bool" where
  "consumed_time_bounded s \<equiv> consumed_time_bounded_2 (consumed_time s) (cur_time s)"

lemmas consumed_time_bounded_def = consumed_time_bounded_2_def

definition current_time_bounded_2 where
  "current_time_bounded_2 k curtime \<equiv>
   unat curtime + unat kernelWCET_ticks + k * unat MAX_PERIOD \<le> unat max_time"

abbreviation current_time_bounded :: "nat \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "current_time_bounded k s \<equiv> current_time_bounded_2 k (cur_time s)"

lemmas current_time_bounded_def = current_time_bounded_2_def

(* unat (cur_time s) + unat kernelWCET_ticks + 2 * unat MAX_SC_PERIOD \<le> unat max_time) *)

\<comment> \<open>A predicate over all the components of state that determine scheduler validity.
    Many operations will preserve all of these.\<close>

abbreviation last_machine_time_of :: "'z state \<Rightarrow> time" where
  "last_machine_time_of s \<equiv> last_machine_time (machine_state s)"

abbreviation time_state_of :: "'z state \<Rightarrow> nat" where
  "time_state_of s \<equiv> time_state (machine_state s)"

type_synonym valid_sched_t
  = "time
     \<Rightarrow> domain
     \<Rightarrow> obj_ref
     \<Rightarrow> obj_ref
     \<Rightarrow> (domain \<Rightarrow> priority \<Rightarrow> obj_ref list)
     \<Rightarrow> obj_ref list
     \<Rightarrow> scheduler_action
     \<Rightarrow> (obj_ref \<rightharpoonup> etcb)
     \<Rightarrow> (obj_ref \<rightharpoonup> thread_state)
     \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option)
     \<Rightarrow> (obj_ref \<rightharpoonup> fault option)
     \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg)
     \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref list)
     \<Rightarrow> bool"

abbreviation valid_sched_pred :: "valid_sched_t \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_sched_pred P \<equiv>
    \<lambda>s. P (cur_time s) (cur_domain s) (cur_thread s) (idle_thread s)
          (ready_queues s) (release_queue s) (scheduler_action s)
          (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s)
          (sc_refill_cfgs_of s) (sc_replies_of s)"

type_synonym valid_sched_strong_t
  = "time \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref list) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref list)
           \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> time \<Rightarrow> nat \<Rightarrow> valid_sched_t"

\<comment> \<open>Sometimes it's useful to prove preservation of some additional projections,
    even though they are not used in valid_sched.\<close>
abbreviation valid_sched_pred_strong :: "valid_sched_strong_t \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_sched_pred_strong P
   \<equiv> \<lambda>s. valid_sched_pred (P (consumed_time s) (cur_sc s) (ep_send_qs_of s)
                              (ep_recv_qs_of s) (sc_tcbs_of s) (last_machine_time_of s)
                              (time_state_of s)) s"

\<comment> \<open>Adapter for valid_sched_pred\<close>
abbreviation (input) valid_sched_pred_strengthen :: "valid_sched_t \<Rightarrow> valid_sched_strong_t" where
  "valid_sched_pred_strengthen P _ _ _ _ _ _ _ \<equiv> P"

(* FIXME RT: delete?
lemma valid_sched_pred_lift_f:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (a (cur_time s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (cur_time s)\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (b (cur_domain s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (c (cur_thread s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (d (idle_thread s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  assumes e: "\<And>P. \<lbrace>\<lambda>s. P (e (ready_queues s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (f (release_queue s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
  assumes g: "\<And>P. \<lbrace>\<lambda>s. P (g (scheduler_action s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes h: "\<And>P. \<lbrace>\<lambda>s. P (h (last_machine_time_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (last_machine_time_of s)\<rbrace>"
  assumes i: "\<And>P. \<lbrace>\<lambda>s. P (i (etcbs_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
  assumes j: "\<And>P. \<lbrace>\<lambda>s. P (j (tcb_sts_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (tcb_sts_of s)\<rbrace>"
  assumes k: "\<And>P. \<lbrace>\<lambda>s. P (k (tcb_scps_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (tcb_scps_of s)\<rbrace>"
  assumes l: "\<And>P. \<lbrace>\<lambda>s. P (l (tcb_faults_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (tcb_faults_of s)\<rbrace>"
  assumes n: "\<And>P. \<lbrace>\<lambda>s. P (n (sc_refill_cfgs_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (sc_refill_cfgs_of s)\<rbrace>"
  assumes p: "\<And>P. \<lbrace>\<lambda>s. P (p (sc_replies_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (sc_replies_of s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (a (cur_time s)) (b (cur_domain s)) (c (cur_thread s))
                (d (idle_thread s)) (e (ready_queues s)) (f (release_queue s))
                (g (scheduler_action s)) (h (last_machine_time_of s)) (i (etcbs_of s))
                (j (tcb_sts_of s)) (k (tcb_scps_of s)) (l (tcb_faults_of s))
                (n (sc_refill_cfgs_of s)) (p (sc_replies_of s))
              \<and> R s\<rbrace>
         m \<lbrace>\<lambda>rv. valid_sched_pred P\<rbrace>"
  apply (rule validI, clarsimp)
  apply (drule refl[THEN iffD1, where P="P _ _ _ _ _ _ _ _ _ _ _ _ _ _ "])
  apply (frule use_valid, rule_tac P="\<lambda>a. P a _ _ _ _ _ _ _ _ _ _ _ _ _" in a, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>b. P _ b _ _ _ _ _ _ _ _ _ _ _ _" in b, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>c. P _ _ c _ _ _ _ _ _ _ _ _ _ _" in c, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>d. P _ _ _ d _ _ _ _ _ _ _ _ _ _" in d, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>e. P _ _ _ _ e _ _ _ _ _ _ _ _ _" in e, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>f. P _ _ _ _ _ f _ _ _ _ _ _ _ _" in f, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>g. P _ _ _ _ _ _ g _ _ _ _ _ _ _" in g, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>h. P _ _ _ _ _ _ _ h _ _ _ _ _ _" in h, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>i. P _ _ _ _ _ _ _ _ i _ _ _ _ _" in i, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>j. P _ _ _ _ _ _ _ _ _ j _ _ _ _" in j, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>k. P _ _ _ _ _ _ _ _ _ _ k _ _ _" in k, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>l. P _ _ _ _ _ _ _ _ _ _ _ l _ _" in l, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>n. P _ _ _ _ _ _ _ _ _ _ _ _ n _" in n, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>p. P _ _ _ _ _ _ _ _ _ _ _ _ _ p" in p, erule (1) conjI, thin_tac "P _ _ _ _ _ _ _ _ _ _ _ _ _ _")
  by simp

lemmas valid_sched_pred_lift =
  valid_sched_pred_lift_f[where a=id and b=id and c=id and d=id and e=id and f=id and g=id
                            and h=id and i=id and j=id and k=id and l=id and n=id and p=id, simplified]

lemma valid_sched_pred_lift':
  assumes "\<And>P. \<lbrace>\<lambda>s. P (cur_time s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_time s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (last_machine_time_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (last_machine_time_of s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
  assumes "\<And>N P t. \<lbrace>\<lambda>s. N (st_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (st_tcb_at P t s)\<rbrace>"
  assumes "\<And>N P t. \<lbrace>\<lambda>s. N (bound_sc_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (bound_sc_tcb_at P t s)\<rbrace>"
  assumes "\<And>N P t. \<lbrace>\<lambda>s. N (fault_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (fault_tcb_at P t s)\<rbrace>"
  assumes "\<And>N P scp. \<lbrace>\<lambda>s. N (sc_refill_cfg_sc_at P scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_refill_cfg_sc_at P scp s)\<rbrace>"
  assumes "\<And>N P scp. \<lbrace>\<lambda>s. N (sc_replies_sc_at P scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_replies_sc_at P scp s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_sched_pred P s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_sched_pred P\<rbrace>"
  by (rule valid_sched_pred_lift; intro assms valid_sched_heap_proj_lifts)
*)

\<comment> \<open>do_machine_op\<close>

crunches do_machine_op
  for valid_sched_pred_misc[wp]:
    "\<lambda>s. P (cur_time s) (consumed_time s) (cur_domain s) (cur_thread s) (cur_sc s) (idle_thread s)
           (ready_queues s) (release_queue s) (scheduler_action s) (kheap s)"

lemma dmo_valid_sched_pred:
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (last_machine_time s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (time_state s)\<rbrace>"
  shows "do_machine_op f \<lbrace>valid_sched_pred_strong P\<rbrace>"
  by (rule hoare_lift_Pf[where f=last_machine_time_of]
      ; rule hoare_lift_Pf[where f=time_state_of]
      ; intro do_machine_op_valid_sched_pred_misc do_machine_op_machine_state assms)

lemma dmo_valid_sched_pred':
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (last_machine_time s)\<rbrace>"
  assumes "\<And>P. f \<lbrace>\<lambda>s. P (time_state s)\<rbrace>"
  shows "(do_machine_op $ f) \<lbrace>valid_sched_pred_strong P\<rbrace>"
  unfolding fun_app_def by (rule dmo_valid_sched_pred[OF assms])

lemmas dmo_lift_valid_sched_pred[wp] =
  dmo_valid_sched_pred[OF machine_op_lift_machine_times]
  dmo_valid_sched_pred'[OF machine_op_lift_machine_times]

lemmas machine_ops_valid_sched_pred[wp] =
  machine_ops_last_machine_time[THEN dmo_valid_sched_pred]
  machine_ops_last_machine_time[THEN dmo_valid_sched_pred']

\<comment> \<open>Updates that affect bound_sc_obj_tcb_at\<close>

lemma update_sched_context_bound_sc_obj_tcb_at:
  assumes h: "\<And>P. update_sched_context scp f \<lbrace>\<lambda>s. P (h s)\<rbrace>"
  assumes g: "\<And>sc. g (sc_refill_cfg_of sc) = sc_refill_cfg_of (f sc)"
  shows "\<lbrace>\<lambda>s. bound_sc_obj_tcb_at (P (h s)) t s
              \<and> (pred_map_eq (Some scp) (tcb_scps_of s) t \<longrightarrow> pred_map (P (h s) \<circ> g) (sc_refill_cfgs_of s) scp)\<rbrace>
         update_sched_context scp f
         \<lbrace>\<lambda>_ s. bound_sc_obj_tcb_at (P (h s)) t s\<rbrace>"
  apply (rule hoare_lift_Pf2[where f=h, OF _ h])
  apply (wpsimp wp: update_sched_context_wp)
  by (auto simp: vs_all_heap_simps obj_at_kh_kheap_simps g)

lemmas update_sched_context_bound_sc_obj_tcb_at_simple
  = update_sched_context_bound_sc_obj_tcb_at[where h="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF hoare_vcg_prop]

lemmas update_sched_context_bound_sc_obj_tcb_at_cur_time
  = update_sched_context_bound_sc_obj_tcb_at[where h=cur_time, OF update_sched_context_cur_time]

lemma set_refills_bound_sc_obj_tcb_at:
  assumes "\<And>P. update_sched_context scp (sc_refills_update (\<lambda>_. refills)) \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. bound_sc_obj_tcb_at (P (g s)) t s
              \<and> (pred_map_eq (Some scp) (tcb_scps_of s) t
                 \<longrightarrow> pred_map (P (g s) \<circ> scrc_refills_update (\<lambda>_. refills)) (sc_refill_cfgs_of s) scp)\<rbrace>
         set_refills scp refills
         \<lbrace>\<lambda>_ s. bound_sc_obj_tcb_at (P (g s)) t s\<rbrace>"
  unfolding set_refills_def by (rule update_sched_context_bound_sc_obj_tcb_at[OF assms]; simp)

lemmas set_refills_bound_sc_obj_tcb_at_simple
  = set_refills_bound_sc_obj_tcb_at[where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF hoare_vcg_prop]

lemmas set_refills_bound_sc_obj_tcb_at_cur_time
  = set_refills_bound_sc_obj_tcb_at[where g=cur_time, OF update_sched_context_cur_time]

lemma set_refills_bound_sc_obj_tcb_at_refills:
  assumes "\<And>P. update_sched_context scp (sc_refills_update (\<lambda>_. refills)) \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. bound_sc_obj_tcb_at (\<lambda>sc. P (g s) (scrc_refills sc)) t s
              \<and> (pred_map_eq (Some scp) (tcb_scps_of s) t \<longrightarrow> P (g s) refills)\<rbrace>
         set_refills scp refills
         \<lbrace>\<lambda>_ s. bound_sc_obj_tcb_at (\<lambda>sc. P (g s) (scrc_refills sc)) t s\<rbrace>"
  by (wpsimp wp: set_refills_bound_sc_obj_tcb_at[OF assms] simp: vs_all_heap_simps)

lemmas set_refills_bound_sc_obj_tcb_at_refills_simple
  = set_refills_bound_sc_obj_tcb_at_refills[where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF hoare_vcg_prop]

lemmas set_refills_bound_sc_obj_tcb_at_refills_cur_time
  = set_refills_bound_sc_obj_tcb_at_refills[where g=cur_time, OF update_sched_context_cur_time]

lemma bound_sc_obj_tcb_at_set_object_no_change_sc':
  assumes f: "\<And>x. P x (sc_refill_cfg_of (f sc)) = P x (sc_refill_cfg_of sc)"
  assumes g: "\<And>P. update_sched_context scp f \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (g s)) t s) \<and> ko_at (SchedContext sc n) scp s\<rbrace>
         set_object scp (SchedContext (f sc) n)
         \<lbrace>\<lambda>rv s. N (bound_sc_obj_tcb_at (P (g s)) t s)\<rbrace>"
  apply (simp add: vs_all_heap_simps)
  apply (rule hoare_vcg_ex_lift_N_pre_conj[of N], rename_tac scp')
  apply (rule hoare_vcg_conj_lift_N_pre_conj[of N]
         , wpsimp wp: set_object_wp simp: obj_at_def)
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def split_del: if_split simp_del: fun_upd_apply)
  apply (drule use_valid[rotated, OF g]
         , fastforce simp: update_sched_context_def get_object_def set_object_def in_monad)
  by (auto elim!: rsubst[of N] simp: f vs_all_heap_simps)

lemmas bound_sc_obj_tcb_at_set_object_no_change_sc =
  bound_sc_obj_tcb_at_set_object_no_change_sc'
    [where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF _ hoare_vcg_prop, simplified]

lemma update_sched_context_inv_set_object:
  assumes "\<And>sc n.
           \<lbrace>\<lambda>s. P s \<and> ko_at (SchedContext sc n) scp s\<rbrace>
           set_object scp (SchedContext (f sc) n)
           \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "update_sched_context scp f \<lbrace>P\<rbrace>"
  by (wpsimp simp: update_sched_context_def wp: assms get_object_wp)

lemma bound_sc_obj_tcb_at_update_sched_context_no_change':
  assumes "\<And>x sc. P x (sc_refill_cfg_of (f sc)) \<longleftrightarrow> P x (sc_refill_cfg_of sc)"
  assumes "\<And>P. update_sched_context scp f \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "update_sched_context scp f \<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (g s)) t s)\<rbrace>"
  apply (rule update_sched_context_inv_set_object)
  by (rule bound_sc_obj_tcb_at_set_object_no_change_sc'; rule assms)

lemmas bound_sc_obj_tcb_at_update_sched_context_no_change =
  bound_sc_obj_tcb_at_update_sched_context_no_change'
    [where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF _ hoare_vcg_prop, simplified]

lemma bound_sc_obj_tcb_at_set_refills_no_change':
  assumes "\<And>x sc. P x (sc_refill_cfg_of sc\<lparr>scrc_refills := refills\<rparr>) = P x (sc_refill_cfg_of sc)"
  assumes "\<And>P. update_sched_context scp (sc_refills_update (\<lambda>_. refills)) \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "set_refills scp refills \<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (g s)) t s)\<rbrace>"
  unfolding set_refills_def
  by (rule bound_sc_obj_tcb_at_update_sched_context_no_change'; simp add: assms)

lemmas bound_sc_obj_tcb_at_set_refills_no_change =
  bound_sc_obj_tcb_at_set_refills_no_change'
    [where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF _ hoare_vcg_prop, simplified]

lemma bound_sc_obj_tcb_at_set_object_no_change_tcb':
  assumes f: "tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes g: "\<And>P. thread_set f tptr \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (g s)) t s) \<and> ko_at (TCB tcb) tptr s\<rbrace>
         set_object tptr (TCB (f tcb))
         \<lbrace>\<lambda>rv s. N (bound_sc_obj_tcb_at (P (g s)) t s)\<rbrace>"
  supply if_split[split del]
  apply (simp add: vs_all_heap_simps)
  apply (wpsimp wp: set_object_wp simp_del: fun_upd_apply)
  apply (drule use_valid[rotated, OF g]
         , fastforce simp: in_monad thread_set_def get_tcb_ko_at set_object_def get_object_def
                           obj_at_def)
  by (auto elim!: rsubst[of N] simp: obj_at_def f
          split: if_splits cong: conj_cong)

lemmas bound_sc_obj_tcb_at_set_object_no_change_tcb =
  bound_sc_obj_tcb_at_set_object_no_change_tcb'
    [where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF _ hoare_vcg_prop]

lemma thread_set_inv_set_object:
  assumes "\<And>tcb. \<lbrace>\<lambda>s. P s \<and> ko_at (TCB tcb) t s\<rbrace> set_object t (TCB (f tcb)) \<lbrace>\<lambda>rv. P\<rbrace>"
  shows "thread_set f t \<lbrace>P\<rbrace>"
  by (wpsimp simp: thread_set_def wp: assms)

lemma bound_sc_obj_tcb_at_thread_set_no_change':
  assumes f: "\<And>sc. tcb_sched_context (f sc) = tcb_sched_context sc"
  assumes g: "\<And>P. thread_set f tptr \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "thread_set f tptr \<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at (P (g s)) t s)\<rbrace>"
  apply (rule thread_set_inv_set_object)
  by (rule bound_sc_obj_tcb_at_set_object_no_change_tcb'; rule assms)

lemmas bound_sc_obj_tcb_at_thread_set_no_change =
  bound_sc_obj_tcb_at_thread_set_no_change'
    [where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P, OF _ hoare_vcg_prop]

\<comment> \<open>\<close>

lemma is_refill_ready_machine_state_update[simp]:
  "is_refill_ready t (s\<lparr>machine_state := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

crunches thread_set
  for cur_time[wp]: "\<lambda>s. P (cur_time s)"

(* FIXME: are these necessary? *)
lemmas bound_sc_obj_tcb_at_set_object_TCB_cur_time =
  bound_sc_obj_tcb_at_set_object_no_change_tcb'[where g=cur_time, OF _ thread_set_cur_time]

lemmas budget_ready_set_object_no_change_tcb =
  bound_sc_obj_tcb_at_set_object_TCB_cur_time[where P=refill_ready_sc]

lemmas budget_sufficient_set_object_no_change_tcb =
  bound_sc_obj_tcb_at_set_object_no_change_tcb[where P="refill_sufficient_sc 0"]

lemmas bound_sc_obj_tcb_at_set_object_SC_cur_time =
  bound_sc_obj_tcb_at_set_object_no_change_sc'[where g=cur_time, OF _ update_sched_context_cur_time]

lemmas budget_ready_set_object_no_change_sc =
  bound_sc_obj_tcb_at_set_object_SC_cur_time[where P=refill_ready_sc, simplified]

lemmas budget_sufficient_set_object_no_change_sc =
  bound_sc_obj_tcb_at_set_object_no_change_sc[where P="refill_sufficient_sc 0", simplified]

lemma update_sched_context_sc_at_pred_inv':
  assumes "\<And>x sc. P x (proj (f sc)) = P x (proj sc)"
  assumes g: "\<And>P. update_sched_context p' f \<lbrace>\<lambda>s. P (g s)\<rbrace>"
  shows "update_sched_context p' f \<lbrace>\<lambda>s. N (sc_at_ppred proj (P (g s)) p s)\<rbrace>"
  apply (rule hoare_lift_Pf[where f=g, OF _ g])
  apply (wpsimp simp: update_sched_context_def wp: get_object_wp set_object_wp)
  by (clarsimp simp: sc_at_ppred_def obj_at_def assms elim: rsubst[of N])

lemmas update_sched_context_sc_at_pred_inv =
  update_sched_context_sc_at_pred_inv'
    [where g="\<lambda>s. undefined" and P="\<lambda>x. P" for P , OF _ hoare_vcg_prop]

lemmas is_refill_ready_update_sched_context_no_change =
  update_sched_context_sc_at_pred_inv'
    [where proj=refill_hd and P=refill_ready and g=cur_time
     , OF _ update_sched_context_cur_time, folded is_refill_ready_def]

lemmas is_refill_sufficient_update_sched_context_no_change =
  update_sched_context_sc_at_pred_inv
    [where proj=refill_hd and P="refill_sufficient usage" for usage, folded is_refill_sufficient_def]

lemmas budget_ready_thread_set_no_change =
  bound_sc_obj_tcb_at_thread_set_no_change'[where g=cur_time and P=refill_ready_sc, OF _ thread_set_cur_time]

lemmas budget_sufficient_thread_set_no_change =
  bound_sc_obj_tcb_at_thread_set_no_change[where P="refill_sufficient_sc 0"]

lemmas budget_sufficient_update_sched_context_no_change =
  bound_sc_obj_tcb_at_update_sched_context_no_change[where P="refill_sufficient_sc 0", simplified]

lemmas budget_ready_update_sched_context_no_change =
  bound_sc_obj_tcb_at_update_sched_context_no_change'
    [where P=refill_ready_sc and g=cur_time, OF _ update_sched_context_cur_time, simplified]

\<comment> \<open>Misc valid_sched-related predicates\<close>

definition
  valid_idle_etcb_2 :: "(obj_ref \<rightharpoonup> etcb) \<Rightarrow> bool"
where
  "valid_idle_etcb_2 ekh \<equiv> etcb_at' (\<lambda>etcb. etcb_domain etcb = default_domain) ekh idle_thread_ptr"

abbreviation valid_idle_etcb :: "'z state \<Rightarrow> bool" where
  "valid_idle_etcb s \<equiv> valid_idle_etcb_2 (etcbs_of s)"

lemmas valid_idle_etcb_def = valid_idle_etcb_2_def

\<comment> \<open>A weaker consequence of valid_idle that is based on heap projections,
    and is sometimes easier to push through proofs.\<close>
abbreviation idle_thread_is_idle where
  "idle_thread_is_idle s \<equiv> pred_map_eq IdleThreadState (tcb_sts_of s) (idle_thread s)"

lemma valid_idle_idle_thread_is_idle[simp, elim!]:
  "valid_idle s \<Longrightarrow> idle_thread_is_idle s"
  by (auto simp: valid_idle_def pred_tcb_at_def obj_at_def vs_all_heap_simps)

definition in_queue_2 where
  "in_queue_2 q t \<equiv> t \<in> set q"

abbreviation in_release_q where
  "in_release_q t s \<equiv> in_queue_2 (release_queue s) t"

lemma in_release_queue_in_release_q[iff]:
  "in_release_queue t s \<longleftrightarrow> in_release_q t s"
  by (simp add: in_release_queue_def in_queue_2_def)

definition in_queues_2 where
  "in_queues_2 qs t \<equiv> \<exists>d p. t \<in> set (qs d p)"

abbreviation in_ready_q where
  "in_ready_q t s \<equiv> in_queues_2 (ready_queues s) t"

lemmas in_release_q_def = in_queue_2_def[where q="release_queue s" for s]
lemmas in_ready_q_def = in_queues_2_def[where qs="ready_queues s" for s]

abbreviation "not_queued_2 qs t \<equiv> \<not> in_queues_2 qs t"

lemma not_queued_2_def:
  "not_queued_2 qs t \<equiv> \<forall>d p. t \<notin> set (qs d p)"
  by (simp add: in_queues_2_def)

abbreviation not_queued :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "not_queued t s \<equiv> not_queued_2 (ready_queues s) t"

lemmas not_queued_def = not_queued_2_def[where qs="ready_queues s" for s :: "'z state"]

abbreviation etcb_eq' :: "priority \<Rightarrow> domain \<Rightarrow> ('obj_ref \<rightharpoonup> etcb) \<Rightarrow> 'obj_ref \<Rightarrow> bool" where
  "etcb_eq' p d \<equiv> pred_map (\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d)"

abbreviation etcb_eq  :: "priority \<Rightarrow> domain \<Rightarrow> obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "etcb_eq p d t s \<equiv> etcb_eq' p d (etcbs_of s) t"

\<comment> \<open>This version of in_ready_q asserts that the thread is in the correct queue.
    It might be nice to replace in_ready_q with this version.\<close>
definition in_etcb_ready_q_2 where
  "in_etcb_ready_q_2 etcbs qs t \<equiv> \<forall>d p. etcb_eq' p d etcbs t \<longrightarrow> t \<in> set (qs d p)"

abbreviation in_etcb_ready_q where
  "in_etcb_ready_q t s \<equiv> in_etcb_ready_q_2 (etcbs_of s) (ready_queues s) t"

lemma in_etcb_ready_q_2E:
  assumes "in_etcb_ready_q_2 etcbs qs t"
  assumes "\<And>d p. etcb_eq' p d etcbs t \<Longrightarrow> t \<in> set (qs d p) \<Longrightarrow> t \<in> set (qs' d p)"
  shows "in_etcb_ready_q_2 etcbs qs' t"
  using assms by (auto simp: in_etcb_ready_q_2_def)

abbreviation not_in_release_q_2 where
  "not_in_release_q_2 q t \<equiv> \<not> in_queue_2 q t"

lemma not_in_release_q_2_def:
  "not_in_release_q_2 q t \<equiv> t \<notin> set q"
  by (simp add: in_queue_2_def)

abbreviation not_in_release_q :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "not_in_release_q t s \<equiv> not_in_release_q_2 (release_queue s) t"

lemmas not_in_release_q_def = not_in_release_q_2_def[where q="release_queue s" for s :: "'z state"]

(* release_queue *)

lemma get_tcb_release_queue_update[simp]: "get_tcb t (release_queue_update f s) = get_tcb t s"
  by (clarsimp simp: get_tcb_def)

lemma get_tcb_scheduler_action_update[simp]: "get_tcb t (scheduler_action_update f s) = get_tcb t s"
  by (clarsimp simp: get_tcb_def)

lemma get_tcb_cdt_update[simp]: "get_tcb t (cdt_update f s) = get_tcb t s"
  by (clarsimp simp: get_tcb_def)

(* FIXME: move *)
lemma map_project_as_opt_map:
  "map_project f m = m |> Some \<circ> f"
  by (fastforce simp: map_project_def opt_map_def split: option.splits)

(* FIXME: move *)
lemma gets_the_map_project:
  "gets_the (map_project f m) = do x \<leftarrow> gets_the m; return (f x) od"
  by (simp add: map_project_as_opt_map)

(* FIXME: move *)
lemma assert_opt_gets_the_K:
  "assert_opt opt = gets_the (K opt)"
  by (simp add: gets_the_def assert_opt_def)

(* FIXME: move *)
lemma gets_gets_the:
  "gets f = gets_the (Some \<circ> f)"
  by (simp add: gets_def gets_the_def)

(* FIXME: move *)
lemma thread_get_gets_the:
  "thread_get f t = gets_the (map_project f (get_tcb t))"
  by (simp add: thread_get_def gets_the_map_project)

(* FIXME: move *)
lemma get_tcb_obj_ref_gets_the:
  "get_tcb_obj_ref f t = gets_the (map_project f (get_tcb t))"
  by (simp add: get_tcb_obj_ref_def thread_get_gets_the)

(* FIXME: move *)
lemma get_sched_context_gets_the:
  "get_sched_context scp = gets_the (\<lambda>s. scs_of s scp)"
  apply (rule ext)
  by (auto simp: get_sched_context_def gets_the_def get_object_def gets_def get_def
                 bind_def return_def fail_def assert_opt_def assert_def sc_heap.all_simps
          split: option.splits kernel_object.splits
          intro: ccontr)

(* FIXME: move *)
definition obind_pair :: "('s \<rightharpoonup> 'a) \<Rightarrow> ('a \<Rightarrow> 's \<rightharpoonup> 'b) \<Rightarrow> 's \<rightharpoonup> 'a \<times> 'b" (infixl "|>|>" 53) where
  "obind_pair f g \<equiv> do { x \<leftarrow> f; map_option (Pair x) \<circ> g x }"

(* FIXME: move *)
lemma gets_the_bind_collapse:
  "do r \<leftarrow> gets_the f; r' \<leftarrow> gets_the (g r); k r r' od
   = do r \<leftarrow> gets_the (f |>|> g); k (fst r) (snd r) od"
  by (fastforce simp: bind_def gets_the_def gets_def get_def assert_opt_def
                      obind_pair_def obind_def return_def fail_def
               split: option.splits)

lemma read_sc_refill_ready_simp:
  "read_sc_refill_ready scp s =
    (case read_sched_context scp s
       of Some sc \<Rightarrow> Some (sc_refill_ready (cur_time s) sc)
        | _ \<Rightarrow> None)"
  by (clarsimp simp: read_sc_refill_ready_def obind_def asks_def split: option.split_asm)

lemma get_sc_refill_ready_gets_the:
  "get_sc_refill_ready scp
   = gets_the (\<lambda>s. map_project (refill_ready_sc (cur_time s)) (sc_refill_cfgs_of s) scp)"
  apply (rule ext)
  apply (clarsimp simp: get_sc_refill_ready_def gets_the_def exec_gets)
  by (simp add: read_sc_refill_ready_simp read_sched_context_def obind_def
                sc_refill_cfgs.all_simps assert_opt_def map_project_simps omonad_defs
         split: option.splits kernel_object.splits)

lemma get_sc_refill_sufficient_gets_the:
  "get_sc_refill_sufficient scp usage = gets_the (\<lambda>s. map_project (refill_sufficient_sc usage) (sc_refill_cfgs_of s) scp)"
  apply (simp add: get_sc_refill_sufficient_def get_sched_context_gets_the
                   gets_the_map_project[symmetric])
  by (auto intro!: arg_cong[where f=gets_the] map_eqI simp: map_project_simps vs_all_heap_simps)

(* FIXME: Move up. Perhaps use more widely, to get rid of pred_map2? *)
definition tcb_sc_refill_cfgs_2 ::
  "(obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> obj_ref \<rightharpoonup> sc_refill_cfg"
  where
  "tcb_sc_refill_cfgs_2 tcb_scps sc_refill_cfgs \<equiv> map_join tcb_scps |> sc_refill_cfgs"

abbreviation "tcb_sc_refill_cfgs_of_kh kh \<equiv> tcb_sc_refill_cfgs_2 (tcb_scps_of_kh kh) (sc_refill_cfgs_of_kh kh)"
abbreviation "tcb_sc_refill_cfgs_of s \<equiv> tcb_sc_refill_cfgs_2 (tcb_scps_of s) (sc_refill_cfgs_of s)"

definition "sc_ready_time \<equiv> r_time \<circ> hd \<circ> scrc_refills"

definition sc_ready_times_2 :: "(obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> obj_ref \<rightharpoonup> time" where
  "sc_ready_times_2 \<equiv> map_project sc_ready_time"

lemmas tcb_ready_times_defs = tcb_sc_refill_cfgs_2_def sc_ready_times_2_def sc_ready_time_def

(* FIXME: these abbreviations don't fire in the right order when printing *)
abbreviation "sc_ready_times_of_kh kh \<equiv> sc_ready_times_2 (sc_refill_cfgs_of_kh kh)"
abbreviation "sc_ready_times_of s \<equiv> sc_ready_times_of_kh (kheap s)"

abbreviation "tcb_ready_times_of_kh kh \<equiv> sc_ready_times_2 (tcb_sc_refill_cfgs_of_kh kh)"
abbreviation "tcb_ready_times_of s \<equiv> sc_ready_times_2 (tcb_sc_refill_cfgs_of s)"

abbreviation "tcb_ready_time_kh t kh \<equiv> the (tcb_ready_times_of_kh kh t)"
abbreviation "tcb_ready_time t s \<equiv> the (tcb_ready_times_of s t)"

(* FIXME: move *)
lemma option_eqI:
  assumes "opt = None \<longleftrightarrow> opt' = None"
  assumes "\<And>x. opt = Some x \<longleftrightarrow> opt' = Some x"
  shows "opt = opt'"
  by (cases opt; simp add: assms)

lemma bound_sc_obj_tcb_at_eqI:
  assumes "kheap s t = Some (TCB tcb)"
          "tcb_sched_context tcb = Some scp"
          "kheap s scp = Some (SchedContext sc n)"
  shows "bound_sc_obj_tcb_at ((=) (sc_refill_cfg_of sc)) t s"
  using assms by (auto simp: vs_all_heap_simps)

lemma budget_sufficient_has_ready_time:
  assumes "bound_sc_obj_tcb_at P t s"
  shows "\<exists>rt. tcb_ready_times_of s t = Some rt"
  using assms
  by (auto simp: opt_map_simps map_join_simps map_project_simps pred_map_simps tcb_ready_times_defs)

(* FIXME: move *)
lemma map_snd_zip':
  "length xs \<ge> length ys \<Longrightarrow> map snd (zip xs ys) = ys"
  by (metis length_map length_zip map_snd_zip_prefix min_absorb2 not_prefixI)

lemma Ball_zip_P_snd:
  assumes "length xs \<ge> length ys"
  shows "(\<forall>x\<in>set (zip xs ys). P (snd x)) \<longleftrightarrow> (\<forall>x\<in>set ys. P x)"
  using assms
proof (induct ys arbitrary: xs)
  case (Cons y ys) thus ?case by (cases xs) auto
qed auto

lemma f_sort_snd_zip:
  "sorted_wrt (img_ord f op) ls \<longleftrightarrow> sorted_wrt (img_ord snd op) (zip ls (map f ls))"
  by (induction ls; simp add: img_ord_def Ball_zip_P_snd)

lemma get_sc_time_wp:
  "\<lbrace>\<lambda>s. \<forall>rt. tcb_ready_times_of s t = Some rt \<longrightarrow> P rt s\<rbrace> get_sc_time t \<lbrace>P\<rbrace>"
  apply (wpsimp simp: get_sc_time_def get_tcb_sc_def tcb_ready_times_defs wp: get_tcb_obj_ref_wp)
  by (auto simp: obj_at_kh_kheap_simps vs_all_heap_simps map_project_simps opt_map_simps map_join_simps)

(* FIXME: move *)
lemma mapM_wp_lift:
  assumes "\<And>Q x. \<lbrace>\<lambda>s. \<forall>rv. P s x rv \<longrightarrow> Q rv s\<rbrace> f x \<lbrace>Q\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>rvs. list_all2 (P s) xs rvs \<longrightarrow> Q rvs s\<rbrace> mapM f xs \<lbrace>Q\<rbrace>"
proof (induct xs arbitrary: Q)
  case Nil thus ?case by (wpsimp simp: mapM_Nil)
next
  case (Cons x xs) show ?case by (wpsimp simp: mapM_Cons wp: Cons assms)
qed

(* FIXME: move *)
lemma list_all2_eq_iff_map_eq_map:
  "list_all2 (\<lambda>x y. f x = g y) xs ys \<longleftrightarrow> map f xs = map g ys"
proof (induct xs arbitrary: ys)
  case (Cons x xs) thus ?case by (cases ys) auto
qed auto

lemma mapM_get_sc_time_wp:
  "\<lbrace>\<lambda>s. \<forall>rt. map (tcb_ready_times_of s) ts = map Some rt \<longrightarrow> P rt s\<rbrace> mapM get_sc_time ts \<lbrace>P\<rbrace>"
  by (wpsimp wp: mapM_wp_lift get_sc_time_wp simp: list_all2_eq_iff_map_eq_map)

(* FIXME move *)
lemma get_sc_time_sp:
  "\<lbrace>P\<rbrace> get_sc_time t \<lbrace>\<lambda>rv s. P s \<and> tcb_ready_times_of s t = Some rv\<rbrace>"
  by (wpsimp wp: get_sc_time_wp)

lemma get_sc_time_sp':
  "\<lbrace>P\<rbrace> get_sc_time t \<lbrace>\<lambda>rv s. P s \<and> rv = tcb_ready_time t s\<rbrace>"
  by (wpsimp wp: get_sc_time_wp)

lemma mapM_get_sc_time_sp:
  "\<lbrace>P\<rbrace> mapM get_sc_time ts \<lbrace>\<lambda>rv s. P s \<and> map (tcb_ready_times_of s) ts = map Some rv\<rbrace>"
  by (wpsimp wp: mapM_get_sc_time_wp)

(* FIXME: move *)
lemma map_Some_implies_map_the:
  assumes "xs = map Some ys"
  shows "ys = map the xs"
  using assms by auto

lemma mapM_get_sc_time_sp':
  "\<lbrace>P\<rbrace> mapM get_sc_time ts \<lbrace>\<lambda>rv s. P s \<and> rv = map (\<lambda>t. tcb_ready_time t s) ts\<rbrace>"
  by (wpsimp wp: mapM_get_sc_time_wp) (auto dest!: map_Some_implies_map_the)

(* FIXME move *)
lemma filter_zip_split:
 "map fst (filter (\<lambda>x. P (snd x)) (zip ls (map f ls)))
    = filter (\<lambda>x. P (f x)) ls"
  by (induction ls; clarsimp)

(* FIXME move *)
lemma sorted_dropWhile_mono:
  "\<lbrakk>sorted ls; t \<in> set (dropWhile P ls); \<forall>x y. x \<le> y \<longrightarrow> P y \<longrightarrow> P x\<rbrakk> \<Longrightarrow> \<not> P t "
  by (induction ls; fastforce)

(* FIXME move *)
lemma sorted_wrt_dropWhile_mono:
  "\<lbrakk>sorted_wrt (\<lambda>x y. f x \<le> f y) ls;
    t \<in> set (dropWhile P ls); \<forall>x y. f x \<le> f y \<longrightarrow> P y \<longrightarrow> P x\<rbrakk> \<Longrightarrow> \<not> P t "
  by (induction ls; auto split: if_split_asm)

definition valid_ready_queued_thread_2 where
  "valid_ready_queued_thread_2 curtime etcbs tcb_sts tcb_scps sc_refill_cfgs t d p \<equiv>
    pred_map (\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d) etcbs t
    \<and> pred_map runnable tcb_sts t
    \<and> released_sc_tcb_at_pred curtime tcb_scps sc_refill_cfgs t"

type_synonym valid_ready_qs_t
  = "(domain \<Rightarrow> priority \<Rightarrow> obj_ref list)
     \<Rightarrow> time
     \<Rightarrow> (obj_ref \<rightharpoonup> etcb)
     \<Rightarrow> (obj_ref \<rightharpoonup> thread_state)
     \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option)
     \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg)
     \<Rightarrow> bool"

definition valid_ready_qs_2 :: valid_ready_qs_t where
  "valid_ready_qs_2 queues curtime etcbs tcb_sts tcb_scps sc_refill_cfgs \<equiv>
    \<forall>d p. (\<forall>t \<in> set (queues d p). valid_ready_queued_thread_2 curtime etcbs tcb_sts tcb_scps
                                                              sc_refill_cfgs t d p)
          \<and> distinct (queues d p)"

abbreviation valid_ready_qs_pred :: "valid_ready_qs_t \<Rightarrow> 'z state \<Rightarrow> bool" where
  "valid_ready_qs_pred P \<equiv>
    \<lambda>s. P (ready_queues s) (cur_time s) (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

abbreviation valid_ready_qs :: "'z state \<Rightarrow> bool" where
  "valid_ready_qs \<equiv> valid_ready_qs_pred valid_ready_qs_2"

lemmas valid_ready_qs_def = valid_ready_qs_2_def valid_ready_queued_thread_2_def

\<comment> \<open>This predicate is currently used only in refill_update_valid_refills, in particular,
    to show that performing refill_update will not result in overflow.
    The constant 2 is required because refill_update will schedule a refill at most MAX_PERIOD
    from the head r_time, of r_amount at most MAX_PERIOD\<close>
definition bounded_release_time_2 :: "time \<Rightarrow> bool" where
  "bounded_release_time_2 reltime \<equiv>
     unat reltime + 2 * unat MAX_PERIOD \<le> unat max_time"

abbreviation cfg_bounded_release_time :: "sc_refill_cfg \<Rightarrow> bool" where
  "cfg_bounded_release_time cfg \<equiv>
     bounded_release_time_2 (r_time (hd (scrc_refills cfg)))"

abbreviation bounded_release_time :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "bounded_release_time scp s \<equiv>
     pred_map (cfg_bounded_release_time) (sc_refill_cfgs_of s) scp"

lemmas cfg_bounded_release_time_def = bounded_release_time_2_def
lemmas bounded_release_time_def = bounded_release_time_2_def

\<comment> \<open>active_sc_valid_refills\<close>

definition active_sc_valid_refills_2 :: "time \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> bool" where
  "active_sc_valid_refills_2 curtime sc_refill_cfgs \<equiv>
   \<forall>scp. pred_map active_scrc sc_refill_cfgs scp
         \<longrightarrow> pred_map cfg_valid_refills sc_refill_cfgs scp
             \<and> pred_map cfg_bounded_release_time sc_refill_cfgs scp"

abbreviation active_sc_valid_refills :: "'z state \<Rightarrow> bool" where
  "active_sc_valid_refills s \<equiv> active_sc_valid_refills_2 (cur_time s) (sc_refill_cfgs_of s)"

lemmas active_sc_valid_refills_def = active_sc_valid_refills_2_def

lemma active_sc_valid_refills_lift_pre_conj:
  assumes a: "\<And>scp. \<lbrace>\<lambda>s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp \<and> R s\<rbrace>
                  f
                  \<lbrace>\<lambda>rv s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) scp\<rbrace>"
  assumes b: "\<And>scp. \<lbrace>\<lambda>s. valid_refills scp s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. valid_refills scp s\<rbrace>"
  assumes c: "\<And>scp. \<lbrace>\<lambda>s. bounded_release_time scp s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. bounded_release_time scp s\<rbrace>"
    shows "\<lbrace>\<lambda>s. active_sc_valid_refills s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. active_sc_valid_refills\<rbrace>"
  apply (simp add: active_sc_valid_refills_def)
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' a b c)

\<comment> \<open>Adapter for valid_sched_pred\<close>
abbreviation (input) valid_sched_valid_ready_qs :: valid_sched_t where
  "valid_sched_valid_ready_qs ctime cdom ct it rq rlq sa etcbs tcb_sts
                         tcb_scps tcb_faults sc_refill_cfgs sc_reps\<equiv>
    valid_ready_qs_2 rq ctime etcbs tcb_sts tcb_scps sc_refill_cfgs"

lemma valid_ready_qsE:
  assumes v: "valid_ready_qs_2 qs ctime etcbs sts scps cfgs"
  assumes t: "\<And>d p. (distinct (qs d p) \<longrightarrow> distinct (qs' d p))
                     \<and> (\<forall>t \<in> set (qs' d p).
                           (t \<in> set (qs d p) \<longrightarrow> valid_ready_queued_thread_2 ctime etcbs sts scps cfgs t d p)
                           \<longrightarrow> valid_ready_queued_thread_2 ctime' etcbs' sts' scps' cfgs' t d p)"
  shows "valid_ready_qs_2 qs' ctime' etcbs' sts' scps' cfgs'"
  using assms by (simp add: valid_ready_qs_2_def)

fun opt_ord where
  "opt_ord (Some x) (Some y) = (x \<le> y)"
| "opt_ord x y = (y = None \<longrightarrow> x = None)"

definition sorted_release_q_2  ::
  "(obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> obj_ref list \<Rightarrow> bool"
  where
  "sorted_release_q_2 tcb_sc_refill_cfgs
   \<equiv> sorted_wrt (img_ord (sc_ready_times_2 tcb_sc_refill_cfgs) opt_ord)"

abbreviation sorted_release_q :: "'z state \<Rightarrow> bool" where
  "sorted_release_q s \<equiv> sorted_release_q_2 (tcb_sc_refill_cfgs_of s) (release_queue s)"

lemmas sorted_release_q_def = sorted_release_q_2_def

definition valid_release_q_except_set_2 ::
  "obj_ref set \<Rightarrow> obj_ref list \<Rightarrow> (obj_ref \<rightharpoonup> thread_state) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> bool"
  where
  "valid_release_q_except_set_2 except queue tcb_sts tcb_scps sc_refill_cfgs \<equiv>
    (\<forall>t \<in> set queue - except. pred_map runnable tcb_sts t
                              \<and> active_sc_tcb_at_pred tcb_scps sc_refill_cfgs t)
    \<and> distinct queue
    \<and> sorted_release_q_2 (tcb_sc_refill_cfgs_2 tcb_scps sc_refill_cfgs) queue"

abbreviation (input) valid_release_q_pred ::
  "(obj_ref list \<Rightarrow>
    (obj_ref \<rightharpoonup> thread_state) \<Rightarrow>
    (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow>
    (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow>
    bool) \<Rightarrow>
   'z state \<Rightarrow> bool"
  where
  "valid_release_q_pred P \<equiv>
    \<lambda>s. P (release_queue s) (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

abbreviation valid_release_q_except_set :: "obj_ref set \<Rightarrow> 'z state \<Rightarrow> bool" where
  "valid_release_q_except_set except s \<equiv> valid_release_q_except_set_2 except (release_queue s) (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

abbreviation "valid_release_q_except_2 t \<equiv> valid_release_q_except_set_2 {t}"
abbreviation "valid_release_q_except t s \<equiv> valid_release_q_except_2 t (release_queue s) (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"
abbreviation "valid_release_q_2 \<equiv> valid_release_q_except_set_2 {}"
abbreviation "valid_release_q s \<equiv> valid_release_q_2 (release_queue s) (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

lemmas valid_release_q_except_set_def = valid_release_q_except_set_2_def
lemmas valid_release_q_except_def = valid_release_q_except_set_2_def
lemmas valid_release_q_def = valid_release_q_except_set_2_def

lemma valid_release_q_distinct[elim!]: "valid_release_q s \<Longrightarrow> distinct (release_queue s)"
  by (clarsimp simp: valid_release_q_def)

definition ready_or_release_2 where
  "ready_or_release_2 ready_qs release_q \<equiv> \<forall>t. \<not> (in_queues_2 ready_qs t \<and> in_queue_2 release_q t)"

abbreviation ready_or_release :: "'z state  \<Rightarrow> bool" where
  "ready_or_release s \<equiv> ready_or_release_2 (ready_queues s) (release_queue s)"

lemmas ready_or_release_def
  = ready_or_release_2_def[of "ready_queues s" "release_queue s" for s :: "'z state"]

lemma ready_or_released_in_ready_qs:
  "ready_or_release s \<Longrightarrow> in_ready_q t s \<Longrightarrow> not_in_release_q t s"
  by (clarsimp simp: ready_or_release_def)

lemma ready_or_released_in_release_queue:
  "ready_or_release s \<Longrightarrow> in_release_queue t s \<Longrightarrow> not_queued t s"
  by (clarsimp simp: ready_or_release_def)

\<comment> \<open>Adapter for valid_sched_pred\<close>
abbreviation (input) valid_sched_valid_release_q :: "obj_ref set \<Rightarrow> valid_sched_t" where
  "valid_sched_valid_release_q S ctime cdom ct it rq rlq sa etcbs tcb_sts
                               tcb_scps tcb_faults sc_refill_cfgs sc_reps\<equiv>
    valid_release_q_except_set_2 S rlq tcb_sts tcb_scps sc_refill_cfgs"

lemma valid_release_qE:
  assumes v: "valid_release_q_except_set_2 except queue tcb_sts tcb_scps sc_refill_cfgs"
  assumes t: "(distinct queue \<longrightarrow> distinct queue')
              \<and> (sorted_release_q_2 (tcb_sc_refill_cfgs_2 tcb_scps sc_refill_cfgs) queue
                 \<longrightarrow> sorted_release_q_2 (tcb_sc_refill_cfgs_2 tcb_scps' sc_refill_cfgs') queue')
              \<and> (\<forall>t \<in> set queue' - except'.
                   (t \<in> set queue - except \<longrightarrow> pred_map runnable tcb_sts t \<and> active_sc_tcb_at_pred tcb_scps sc_refill_cfgs t)
                   \<longrightarrow> pred_map runnable tcb_sts' t \<and> active_sc_tcb_at_pred tcb_scps' sc_refill_cfgs' t)"
  shows "valid_release_q_except_set_2 except' queue' tcb_sts' tcb_scps' sc_refill_cfgs'"
  using v by (simp add: valid_release_q_except_set_2_def t)

\<comment> \<open>Set of all threads in all ready queues\<close>
abbreviation ready_queued_threads_2 :: "(domain \<Rightarrow> priority \<Rightarrow> obj_ref list) \<Rightarrow> obj_ref set" where
  "ready_queued_threads_2 queues \<equiv> {t. \<exists>d p. t \<in> set (queues d p)}"

\<comment> \<open>Set of all threads in all ready queues\<close>
abbreviation ready_queued_threads :: "'z state \<Rightarrow> obj_ref set" where
  "ready_queued_threads s \<equiv> ready_queued_threads_2 (ready_queues s)"

abbreviation released_if_bound_sc_tcb_at_2 ::
  "obj_ref \<Rightarrow> time \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> bool"
  where
  "released_if_bound_sc_tcb_at_2 t curtime tcb_scps sc_refill_cfgs \<equiv>
    pred_map_eq None tcb_scps t \<or> released_sc_tcb_at_pred curtime tcb_scps sc_refill_cfgs t"

abbreviation released_if_bound_sc_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "released_if_bound_sc_tcb_at t s \<equiv> released_if_bound_sc_tcb_at_2 t (cur_time s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

abbreviation active_if_bound_sc_tcb_at_2 ::
  "obj_ref \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> bool"
  where
  "active_if_bound_sc_tcb_at_2 t tcb_scps sc_refill_cfgs \<equiv>
    pred_map_eq None tcb_scps t \<or> active_sc_tcb_at_pred tcb_scps sc_refill_cfgs t"

abbreviation active_if_bound_sc_tcb_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "active_if_bound_sc_tcb_at t s \<equiv> active_if_bound_sc_tcb_at_2 t (tcb_scps_of s) (sc_refill_cfgs_of s)"

type_synonym released_ipc_queues_t
  = "time
     \<Rightarrow> (obj_ref \<rightharpoonup> thread_state)
     \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option)
     \<Rightarrow> (obj_ref \<rightharpoonup> fault option)
     \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg)
     \<Rightarrow> bool"

abbreviation is_blocked_on_recv_ntfn :: "thread_state \<Rightarrow> bool" where
  "is_blocked_on_recv_ntfn st \<equiv> is_blocked_on_receive st \<or> is_blocked_on_ntfn st"

abbreviation is_blocked_on_send_recv :: "thread_state \<Rightarrow> bool" where
  "is_blocked_on_send_recv st \<equiv> is_blocked_on_send st \<or> is_blocked_on_receive st"

abbreviation blocked_on_send_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "blocked_on_send_tcb_at t s \<equiv> pred_map is_blocked_on_send (tcb_sts_of s) t"

abbreviation blocked_on_reply_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "blocked_on_reply_tcb_at t s \<equiv> pred_map is_blocked_on_reply (tcb_sts_of s) t"

abbreviation blocked_on_recv_ntfn_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "blocked_on_recv_ntfn_tcb_at t s \<equiv> pred_map is_blocked_on_recv_ntfn (tcb_sts_of s) t"

abbreviation blocked_on_send_recv_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "blocked_on_send_recv_tcb_at t s \<equiv> pred_map is_blocked_on_send_recv (tcb_sts_of s) t"

definition is_timeout_fault_opt :: "fault option \<Rightarrow> bool" where
  "is_timeout_fault_opt \<equiv> case_option False is_timeout_fault"

abbreviation fault_tcb_at' :: "(fault option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "fault_tcb_at' P t s \<equiv> pred_map P (tcb_faults_of s) t"

abbreviation timeout_faulted_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "timeout_faulted_tcb_at \<equiv> fault_tcb_at' is_timeout_fault_opt"

abbreviation valid_sender_sc_tcb_at_2 ::
  "obj_ref \<Rightarrow> time \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow> (obj_ref \<rightharpoonup> fault option) \<Rightarrow> (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow> bool"
  where
  "valid_sender_sc_tcb_at_2 t curtime tcb_scps tcb_faults sc_refill_cfgs \<equiv>
    pred_map is_timeout_fault_opt tcb_faults t \<and> active_sc_tcb_at_pred tcb_scps sc_refill_cfgs t
    \<or> released_if_bound_sc_tcb_at_2 t curtime tcb_scps sc_refill_cfgs"

abbreviation valid_sender_sc_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "valid_sender_sc_tcb_at t s \<equiv> valid_sender_sc_tcb_at_2 t (cur_time s) (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)"

\<comment> \<open>Sometimes useful for identifying blocked threads that must be released_if_bound_sc_tcb_at\<close>
abbreviation requires_released_if_bound_sc_tcb_at :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "requires_released_if_bound_sc_tcb_at t s
   \<equiv> blocked_on_recv_ntfn_tcb_at t s \<or> blocked_on_send_tcb_at t s \<and> \<not> timeout_faulted_tcb_at t s"

(* FIXME RT: this is no longer a suitable name. *)
definition released_ipc_queued_thread_2 :: "obj_ref \<Rightarrow> released_ipc_queues_t" where
  "released_ipc_queued_thread_2 t curtime tcb_sts tcb_scps tcb_faults sc_refill_cfgs \<equiv>
    (pred_map is_blocked_on_recv_ntfn tcb_sts t \<longrightarrow> released_if_bound_sc_tcb_at_2 t curtime tcb_scps sc_refill_cfgs)
    \<and> (pred_map is_blocked_on_send tcb_sts t \<longrightarrow> valid_sender_sc_tcb_at_2 t curtime tcb_scps tcb_faults sc_refill_cfgs)
    \<and> (pred_map is_blocked_on_reply tcb_sts t \<longrightarrow> active_if_bound_sc_tcb_at_2 t tcb_scps sc_refill_cfgs)"

definition released_ipc_queues_2 ::"released_ipc_queues_t" where
  "released_ipc_queues_2 curtime tcb_sts tcb_scps tcb_faults sc_refill_cfgs \<equiv>
    \<forall>t. released_ipc_queued_thread_2 t curtime tcb_sts tcb_scps tcb_faults sc_refill_cfgs"

abbreviation released_ipc_queues_pred :: "released_ipc_queues_t \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "released_ipc_queues_pred P \<equiv>
    \<lambda>s. P (cur_time s) (tcb_sts_of s) (tcb_scps_of s) (tcb_faults_of s) (sc_refill_cfgs_of s)"
abbreviation released_ipc_queued_thread :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "released_ipc_queued_thread t \<equiv> released_ipc_queues_pred (released_ipc_queued_thread_2 t)"
abbreviation released_ipc_queues :: "'z::state_ext state \<Rightarrow> bool" where
  "released_ipc_queues \<equiv> released_ipc_queues_pred released_ipc_queues_2"

lemmas released_ipc_queues_defs = released_ipc_queued_thread_2_def released_ipc_queues_2_def

lemma released_ipc_queues_blocked_on_recv_ntfn_D:
  assumes "released_ipc_queues_2 curtime tcb_sts tcb_scps tcb_faults sc_refill_cfgs"
  assumes "pred_map is_blocked_on_recv_ntfn tcb_sts t"
  shows "released_if_bound_sc_tcb_at_2 t curtime tcb_scps sc_refill_cfgs"
  using assms unfolding released_ipc_queues_defs by simp

lemma released_ipc_queues_blocked_on_send_D:
  assumes "released_ipc_queues_2 curtime tcb_sts tcb_scps tcb_faults sc_refill_cfgs"
  assumes "pred_map is_blocked_on_send tcb_sts t"
  shows "valid_sender_sc_tcb_at_2 t curtime tcb_scps tcb_faults sc_refill_cfgs"
  using assms unfolding released_ipc_queues_defs by simp

lemma released_ipc_queues_blocked_on_reply_D:
  assumes "released_ipc_queues_2 curtime tcb_sts tcb_scps tcb_faults sc_refill_cfgs"
  assumes "pred_map is_blocked_on_reply tcb_sts t"
  shows "active_if_bound_sc_tcb_at_2 t tcb_scps sc_refill_cfgs"
  using assms unfolding released_ipc_queues_defs by simp

\<comment> \<open>We limit this rule to two assumptions, so we can use as an elim! rule in clarsimp.\<close>
lemma released_ipc_queuesE:
  assumes "released_ipc_queues_2 curtime tcb_sts tcb_scps tcb_faults sc_refill_cfgs"
  assumes "\<And>t. (pred_map is_blocked_on_recv_ntfn tcb_sts' t
                 \<longrightarrow> (pred_map is_blocked_on_recv_ntfn tcb_sts t
                      \<longrightarrow> released_if_bound_sc_tcb_at_2 t curtime tcb_scps sc_refill_cfgs)
                 \<longrightarrow> released_if_bound_sc_tcb_at_2 t curtime' tcb_scps' sc_refill_cfgs')
                \<and> (pred_map is_blocked_on_send tcb_sts' t
                   \<longrightarrow> (pred_map is_blocked_on_send tcb_sts t
                        \<longrightarrow> valid_sender_sc_tcb_at_2 t curtime tcb_scps tcb_faults sc_refill_cfgs)
                   \<longrightarrow> valid_sender_sc_tcb_at_2 t curtime' tcb_scps' tcb_faults' sc_refill_cfgs')
                \<and> (pred_map is_blocked_on_reply tcb_sts' t
                   \<longrightarrow> (pred_map is_blocked_on_reply tcb_sts t
                        \<longrightarrow> active_if_bound_sc_tcb_at_2 t tcb_scps sc_refill_cfgs)
                   \<longrightarrow> active_if_bound_sc_tcb_at_2 t tcb_scps' sc_refill_cfgs')"
  shows "released_ipc_queues_2 curtime' tcb_sts' tcb_scps' tcb_faults' sc_refill_cfgs'"
  using assms by (auto simp: released_ipc_queues_defs)

(* FIXME RT: generalise this pattern *)
lemma active_bound_sc_tcb_at:
  "active_if_bound_sc_tcb_at t s \<Longrightarrow> pred_map_eq (Some scp) (tcb_scps_of s) t \<Longrightarrow> active_sc_tcb_at t s"
  by (clarsimp simp: vs_all_heap_simps)

\<comment> \<open>Adapter for valid_sched_pred\<close>
abbreviation (input) valid_sched_ipc_queues :: valid_sched_t where
  "valid_sched_ipc_queues ctime cdom ct it rq rlq sa etcbs sts scps faults scrcs replies
   \<equiv> released_ipc_queues_2 ctime sts scps faults scrcs"

(* FIXME RT: move *)
lemma ipc_queued_thread_state_def2:
  "ipc_queued_thread_state st \<equiv>
    is_blocked_on_receive st \<or> is_blocked_on_ntfn st \<or> is_blocked_on_send st
    \<or> is_blocked_on_reply st"
  by (clarsimp simp: atomize_eq; cases st; simp)

lemma pred_map_ipc_queued_thread_state_iff:
  "pred_map ipc_queued_thread_state tcb_sts t
   \<longleftrightarrow> pred_map is_blocked_on_recv_ntfn tcb_sts t
       \<or> pred_map is_blocked_on_send tcb_sts t
       \<or> pred_map is_blocked_on_reply tcb_sts t"
  by (auto simp: ipc_queued_thread_state_def2 pred_map_simps is_blocked_thread_state_defs)

(* This is a bit of a compromise; ideally, we should be always using the above,
   but sometimes you don't want to unfold st_tcb_at to pred_map everywhere just yet
   due to dependencies etc. *)
lemma st_tcb_ipc_queued_thread_state_iff:
  "st_tcb_at ipc_queued_thread_state t s
   \<longleftrightarrow> (st_tcb_at is_blocked_on_reply t s \<or>
        st_tcb_at is_blocked_on_recv_ntfn t s \<or>
        st_tcb_at is_blocked_on_send t s)"
  by (fastforce simp: pred_map_ipc_queued_thread_state_iff tcb_at_kh_simps)

(* FIXME RT: move *)
definition ep_queue_of :: "endpoint \<Rightarrow> obj_ref list option"
where
  "ep_queue_of ep \<equiv> case ep of
                      IdleEP \<Rightarrow> None
                    | SendEP x \<Rightarrow> Some x
                    | RecvEP x \<Rightarrow> Some x"

(* FIXME RT: move *)
lemma get_ep_queue_wp':
  "\<lbrace> \<lambda>s. \<forall>q. ep_queue_of ep = Some q \<longrightarrow> Q q s \<rbrace> get_ep_queue ep \<lbrace> Q \<rbrace>"
  by (wpsimp simp: get_ep_queue_def ep_queue_of_def)

(* FIXME RT: move *)
lemma valid_ep_distinct_queue:
  "\<lbrakk>valid_ep ep s; ep_queue_of ep = Some q\<rbrakk> \<Longrightarrow> distinct q"
  by (auto simp: valid_ep_def ep_queue_of_def split: endpoint.splits)

(* FIXME RT: move *)
lemma pred_map_P_not_idle:
  "\<lbrakk>valid_idle s; pred_map P (tcb_sts_of s) t; \<And>st. idle st \<Longrightarrow> \<not> P st\<rbrakk> \<Longrightarrow> t \<noteq> idle_thread s"
  by (clarsimp simp: vs_all_heap_simps valid_idle_def pred_tcb_at_def obj_at_def)

(* FIXME RT: move *)
lemma in_tcb_st_refs_of_iff:
  "(ref, reftype) \<in> tcb_st_refs_of st
   \<longleftrightarrow> (reftype = TCBReply \<and> (st = BlockedOnReply ref
                              \<or> (\<exists>ep receiver_data. st = BlockedOnReceive ep (Some ref) receiver_data)))
       \<or> (reftype = TCBBlockedRecv \<and> (\<exists>ropt receiver_data. st = BlockedOnReceive ref ropt receiver_data))
       \<or> (reftype = TCBBlockedSend \<and> (\<exists>sender_data. st = BlockedOnSend ref sender_data))
       \<or> (reftype = TCBSignal \<and> st = BlockedOnNotification ref)"
  by (cases st) (auto simp: tcb_st_refs_of_def)

(* FIXME RT: move *)
lemma valid_ntfn_distinct_queue:
  "\<lbrakk>valid_ntfn ntfn s; ntfn_obj ntfn = WaitingNtfn q\<rbrakk> \<Longrightarrow> distinct q"
  by (auto simp: valid_ntfn_def split: endpoint.splits)

\<comment> \<open>Lifting rules for IPC queue schedulability.\<close>
lemma released_ipc_queue_lift_pre_conj:
  assumes "\<lbrace>\<lambda>s. \<not> P (blocked_on_send_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P (blocked_on_send_tcb_at t s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. \<not> P (blocked_on_recv_ntfn_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P (blocked_on_recv_ntfn_tcb_at t s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. \<not> P (blocked_on_reply_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rf s. \<not> P (blocked_on_reply_tcb_at t s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. P (timeout_faulted_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (timeout_faulted_tcb_at t s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. P (pred_map_eq None (tcb_scps_of s) t) \<and> R s\<rbrace>
           f \<lbrace>\<lambda>rf s. P (pred_map_eq None (tcb_scps_of s) t)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and> R s\<rbrace>
           f \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. P (budget_ready t s) \<and> R s\<rbrace>
           f \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  assumes "\<lbrace>\<lambda>s. P (budget_sufficient t s) \<and> R s\<rbrace>
           f \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (released_ipc_queued_thread t s) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rf s. P (released_ipc_queued_thread t s)\<rbrace>"
  unfolding released_ipc_queued_thread_2_def released_sc_tcb_at_def
  by (intro hoare_vcg_imp_lift_N_pre_conj hoare_vcg_disj_lift_N_pre_conj hoare_vcg_conj_lift_N_pre_conj assms)

lemmas released_ipc_queue_lift =
  released_ipc_queue_lift_pre_conj[where R=\<top>, simplified]

lemma released_ipc_queues_lift_pre_conj:
  assumes "\<And>t. \<lbrace>\<lambda>s. \<not> P (blocked_on_send_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P (blocked_on_send_tcb_at t s)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. \<not> P (blocked_on_recv_ntfn_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> P (blocked_on_recv_ntfn_tcb_at t s)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. \<not> P (blocked_on_reply_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rf s. \<not> P (blocked_on_reply_tcb_at t s)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. P (timeout_faulted_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (timeout_faulted_tcb_at t s)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. P (pred_map_eq None (tcb_scps_of s) t) \<and> R s\<rbrace>
                f \<lbrace>\<lambda>rf s. P (pred_map_eq None (tcb_scps_of s) t)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and> R s\<rbrace>
                f \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. P (budget_ready t s) \<and> R s\<rbrace>
                f \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. P (budget_sufficient t s) \<and> R s\<rbrace>
                f \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (released_ipc_queues s) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rf s. P (released_ipc_queues s)\<rbrace>"
  unfolding released_ipc_queues_2_def
  by (intro hoare_vcg_all_lift_N_pre_conj released_ipc_queue_lift_pre_conj assms)

lemmas released_ipc_queues_lift =
  released_ipc_queues_lift_pre_conj[where R=\<top>, simplified]

lemma released_ipc_queues_pred_lift_f:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (a (cur_time s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (cur_time s)\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (b (tcb_sts_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (tcb_sts_of s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (c (tcb_scps_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (tcb_scps_of s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (d (tcb_faults_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (tcb_faults_of s)\<rbrace>"
  assumes e: "\<And>P. \<lbrace>\<lambda>s. P (e (sc_refill_cfgs_of s)) \<and> R s\<rbrace> m \<lbrace>\<lambda>rv s. P (sc_refill_cfgs_of s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (a (cur_time s))
                (b (tcb_sts_of s))
                (c (tcb_scps_of s))
                (d (tcb_faults_of s))
                (e (sc_refill_cfgs_of s))
              \<and> R s\<rbrace>
         m \<lbrace>\<lambda>rv. released_ipc_queues_pred P\<rbrace>"
  apply (rule validI, clarsimp)
  apply (drule refl[THEN iffD1, where P="P _ _ _ _ _"])
  apply (frule use_valid, rule_tac P="\<lambda>a. P a _ _ _ _" in a, erule (1) conjI, thin_tac "P _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>b. P _ b _ _ _" in b, erule (1) conjI, thin_tac "P _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>c. P _ _ c _ _" in c, erule (1) conjI, thin_tac "P _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>d. P _ _ _ d _" in d, erule (1) conjI, thin_tac "P _ _ _ _ _")
  apply (frule use_valid, rule_tac P="\<lambda>e. P _ _ _ _ e" in e, erule (1) conjI, thin_tac "P _ _ _ _ _")
  by assumption

lemmas released_ipc_queues_pred_lift_f' =
  released_ipc_queues_pred_lift_f[where R=\<top>, simplified]

lemma released_ipc_queues_pred_lift:
  assumes "\<And>P. \<lbrace>\<lambda>s. P (cur_time s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_time s)\<rbrace>"
  assumes "\<And>N P t. \<lbrace>\<lambda>s. N (st_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (st_tcb_at P t s)\<rbrace>"
  assumes "\<And>N P t. \<lbrace>\<lambda>s. N (bound_sc_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (bound_sc_tcb_at P t s)\<rbrace>"
  assumes "\<And>N P t. \<lbrace>\<lambda>s. N (fault_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (fault_tcb_at P t s)\<rbrace>"
  assumes "\<And>N P scp. \<lbrace>\<lambda>s. N (sc_refill_cfg_sc_at P scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_refill_cfg_sc_at P scp s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. released_ipc_queues_pred P s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. released_ipc_queues_pred P\<rbrace>"
  by (rule released_ipc_queues_pred_lift_f; intro assms valid_sched_heap_proj_lifts)

lemmas released_ipc_queues_pred_lift' =
  released_ipc_queues_pred_lift[where R=\<top>, simplified]

lemma bound_sc_obj_tcb_at_kh_lift_strong:
  assumes curtime:
    "\<And>P. \<lbrace>\<lambda>s. P (g s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (g s)\<rbrace>"
  assumes bound_sc:
    "\<And>x. \<lbrace>\<lambda>s. N (\<exists>p. pred_map_eq (Some p) (tcb_scps_of_kh (heap s)) t
                      \<and> pred_map (P x) (sc_refill_cfgs_of_kh (heap s)) p)
               \<and> R s\<rbrace>
          f \<lbrace>\<lambda>rv s. N (\<exists>p. pred_map_eq (Some p) (tcb_scps_of_kh (heap s)) t
                            \<and> pred_map (P x) (sc_refill_cfgs_of_kh (heap s)) p)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at_kh (P (g s)) (heap s) t) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rv s. N (bound_sc_obj_tcb_at_kh (P (g s)) (heap s) t)\<rbrace>"
  unfolding pred_map2'_pred_maps
  by (rule hoare_lift_concrete_Pf_pre_conj[where f=g, OF curtime], rule bound_sc)

lemma bound_sc_obj_tcb_at_kh_lift:
  assumes
    "\<And>P. \<lbrace>\<lambda>s. P (g s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (g s)\<rbrace>"
    "\<And>p. \<lbrace>\<lambda>s. N (pred_map_eq (Some p) (tcb_scps_of_kh (heap s)) t) \<and> R s\<rbrace>
          f \<lbrace>\<lambda>rv s. N (pred_map_eq (Some p) (tcb_scps_of_kh (heap s)) t)\<rbrace>"
    "\<And>x p. \<lbrace>\<lambda>s. N (pred_map (P x) (sc_refill_cfgs_of_kh (heap s)) p) \<and> R s\<rbrace>
          f \<lbrace>\<lambda>rv s. N (pred_map (P x) (sc_refill_cfgs_of_kh (heap s)) p)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (bound_sc_obj_tcb_at_kh (P (g s)) (heap s) t) \<and> R s\<rbrace>
         f \<lbrace>\<lambda>rv s. N (bound_sc_obj_tcb_at_kh (P (g s)) (heap s) t)\<rbrace>"
  by (intro bound_sc_obj_tcb_at_kh_lift_strong
            hoare_vcg_ex_lift_N_pre_conj[of N]
            hoare_vcg_conj_lift_N_pre_conj[of N]
            assms)

lemmas bound_sc_obj_tcb_at_lift_strong'
  = bound_sc_obj_tcb_at_kh_lift_strong[where heap="kheap::'z::state_ext state \<Rightarrow> _"
                                       , folded obj_at_kh_kheap_simps
                                       , simplified pred_tcb_at_eq_commute]

lemmas bound_sc_obj_tcb_at_lift_strong =
  bound_sc_obj_tcb_at_lift_strong'[where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P
                                   , OF hoare_vcg_prop_pre_conj]

lemmas bound_sc_obj_tcb_at_lift'
  = bound_sc_obj_tcb_at_kh_lift[where heap="kheap::'z::state_ext state \<Rightarrow> _"
                                , folded obj_at_kh_kheap_simps
                                , simplified pred_tcb_at_eq_commute]

lemmas bound_sc_obj_tcb_at_lift =
  bound_sc_obj_tcb_at_lift'[where g="\<lambda>_. undefined" and P="\<lambda>_. P" for P
                            , OF hoare_vcg_prop_pre_conj]

\<comment> \<open>\<close>
lemma bound_sc_maybe_active[simp]:
  "bound_sc_tcb_at bound t s \<Longrightarrow> bound_sc_tcb_at ((=) None) t s \<or> P \<longleftrightarrow> P"
  by (auto simp: pred_tcb_at_def obj_at_def)

(* FIXME: makes naming consistent with _2 convention *)
\<comment> \<open>Switches nq and nr allow us to make various claims about presence in queues\<close>
definition valid_blocked_thread where
  "valid_blocked_thread nq nr except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t \<equiv>
   pred_map active tcb_sts t \<longrightarrow> active_sc_tcb_at_pred tcb_scps sc_refill_cfgs t
   \<longrightarrow> t \<in> except \<or> nq (in_queues_2 queues t) \<or> nr (in_queue_2 rlq t) \<or> t = ct \<or> sa = switch_thread t"

lemma valid_blocked_thread_bot_queues:
  "valid_blocked_thread \<bottom> nr except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t
   \<Longrightarrow> valid_blocked_thread nq nr except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t"
  by (auto simp: valid_blocked_thread_def)

lemma valid_blocked_thread_bot_release_q:
  "valid_blocked_thread nq \<bottom> except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t
   \<Longrightarrow> valid_blocked_thread nq nr except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t"
  by (auto simp: valid_blocked_thread_def)

abbreviation valid_blocked_thread_kh where
  "valid_blocked_thread_kh nq nr except queues rlq sa ct kh
   \<equiv> valid_blocked_thread nq nr except queues rlq sa ct
                          (tcb_sts_of_kh kh) (tcb_scps_of_kh kh) (sc_refill_cfgs_of_kh kh)"

abbreviation valid_blocked_thread_of ::
  "(bool \<Rightarrow> bool) \<Rightarrow> (bool \<Rightarrow> bool) \<Rightarrow> obj_ref set \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  where
  "valid_blocked_thread_of nq nr except t s
   \<equiv> valid_blocked_thread nq nr except
                          (ready_queues s) (release_queue s) (scheduler_action s) (cur_thread s)
                          (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s) t"

abbreviation valid_blocked_tcb_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_blocked_tcb_at \<equiv> valid_blocked_thread_of id id {}"

definition in_ntfn_q where
  "in_ntfn_q t s \<equiv> \<exists>ptr. ntfn_at_pred (\<lambda>n. t \<in> set (ntfn_queue (ntfn_obj n))) ptr s"

(*** valid_blocked ***)

definition valid_blocked_except_set_2 where
  "valid_blocked_except_set_2 except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs \<equiv>
    \<forall>t. valid_blocked_thread id id except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t"

lemmas valid_blocked_defs = valid_blocked_thread_def valid_blocked_except_set_2_def

abbreviation valid_blocked_except_set_kh where
  "valid_blocked_except_set_kh except queues rlq sa ct kh \<equiv>
    valid_blocked_except_set_2 except queues rlq sa ct
                               (tcb_sts_of_kh kh) (tcb_scps_of_kh kh) (sc_refill_cfgs_of_kh kh)"

abbreviation valid_blocked_pred ::
  "((domain \<Rightarrow> priority \<Rightarrow> obj_ref list) \<Rightarrow>
    obj_ref list \<Rightarrow>
    scheduler_action \<Rightarrow>
    obj_ref \<Rightarrow>
    (obj_ref \<rightharpoonup> thread_state) \<Rightarrow>
    (obj_ref \<rightharpoonup> obj_ref option) \<Rightarrow>
    (obj_ref \<rightharpoonup> sc_refill_cfg) \<Rightarrow>
    bool) \<Rightarrow>
   'z::state_ext state \<Rightarrow> bool" where
 "valid_blocked_pred P \<equiv>
    \<lambda>s. P (ready_queues s) (release_queue s) (scheduler_action s) (cur_thread s)
          (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

abbreviation valid_blocked_except_set :: "obj_ref set \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_blocked_except_set except \<equiv> valid_blocked_pred (valid_blocked_except_set_2 except)"

abbreviation "valid_blocked_except_2 t \<equiv> valid_blocked_except_set_2 {t}"
abbreviation "valid_blocked_except t \<equiv> valid_blocked_pred (valid_blocked_except_2 t)"
abbreviation "valid_blocked_2 \<equiv> valid_blocked_except_set_2 {}"
abbreviation "valid_blocked \<equiv> valid_blocked_pred valid_blocked_2"

lemma valid_blockedE:
  assumes "valid_blocked_except_set_2 except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  assumes "\<And>t. valid_blocked_thread id id except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t
                \<longrightarrow> valid_blocked_thread id id except' queues' rlq' sa' ct' tcb_sts' tcb_scps' sc_refill_cfgs' t"
  shows "valid_blocked_except_set_2 except' queues' rlq' sa' ct' tcb_sts' tcb_scps' sc_refill_cfgs'"
  using assms by (auto simp: valid_blocked_except_set_2_def)

lemma valid_blockedE':
  assumes v: "valid_blocked_except_set_2 except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  assumes t: "\<And>t. pred_map active tcb_sts' t \<longrightarrow> active_sc_tcb_at_pred tcb_scps' sc_refill_cfgs' t
                   \<longrightarrow> (pred_map active tcb_sts t \<longrightarrow> active_sc_tcb_at_pred tcb_scps sc_refill_cfgs t
                        \<longrightarrow> t \<in> except \<or> in_queues_2 queues t \<or> in_queue_2 rlq t \<or> t = ct \<or> sa = switch_thread t)
                   \<longrightarrow> t \<in> except' \<or> in_queues_2 queues' t \<or> in_queue_2 rlq' t \<or> t = ct' \<or> sa' = switch_thread t"
  shows "valid_blocked_except_set_2 except' queues' rlq' sa' ct' tcb_sts' tcb_scps' sc_refill_cfgs'"
  apply (rule valid_blockedE[OF v])
  using t by (simp add: valid_blocked_thread_def)

lemma valid_blockedD:
  "valid_blocked_except_set_2 except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs
   \<Longrightarrow> valid_blocked_thread id id except queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs t"
  by (auto simp: valid_blocked_except_set_2_def)

\<comment> \<open>Adapter for valid_sched_pred\<close>
abbreviation (input) valid_sched_valid_blocked :: "obj_ref set \<Rightarrow> valid_sched_t" where
  "valid_sched_valid_blocked S ctime cdom ct it rq rlq sa etcbs tcb_sts
                         tcb_scps tcb_faults sc_refill_cfgs sc_reps \<equiv>
    valid_blocked_except_set_2 S rq rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"

definition in_cur_domain_2 where
  "in_cur_domain_2 thread cdom ekh \<equiv> etcb_at' (\<lambda>t. etcb_domain t = cdom) ekh thread"

abbreviation in_cur_domain :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "in_cur_domain thread s \<equiv> in_cur_domain_2 thread (cur_domain s) (etcbs_of s)"

lemmas in_cur_domain_def = in_cur_domain_2_def

definition ct_in_cur_domain_2 where
  "ct_in_cur_domain_2 thread thread' sa cdom ekh \<equiv>
     sa = resume_cur_thread \<longrightarrow> thread = thread' \<or> in_cur_domain_2 thread cdom ekh"

abbreviation ct_in_cur_domain where
  "ct_in_cur_domain s \<equiv>
    ct_in_cur_domain_2 (cur_thread s) (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)"

lemmas ct_in_cur_domain_def = ct_in_cur_domain_2_def

definition is_activatable_2 where
  "is_activatable_2 thread sa tcb_sts \<equiv> sa = resume_cur_thread \<longrightarrow> pred_map activatable tcb_sts thread"

abbreviation is_activatable :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool"  where
  "is_activatable thread s \<equiv> is_activatable_2 thread (scheduler_action s) (tcb_sts_of s)"

lemmas is_activatable_def = is_activatable_2_def

definition weak_valid_sched_action_2 where
  "weak_valid_sched_action_2 except curtime sa release_q tcb_sts tcb_scps sc_refill_cfgs \<equiv>
    \<forall>t. sa = switch_thread t \<and> t \<notin> except
        \<longrightarrow> pred_map runnable tcb_sts t
            \<and> released_sc_tcb_at_pred curtime tcb_scps sc_refill_cfgs t
            \<and> \<not> t \<in> set release_q"

abbreviation weak_valid_sched_action:: "'z state \<Rightarrow> bool" where
  "weak_valid_sched_action s \<equiv>
    weak_valid_sched_action_2 {} (cur_time s) (scheduler_action s) (release_queue s) (tcb_sts_of s)
                                 (tcb_scps_of s) (sc_refill_cfgs_of s)"

lemmas weak_valid_sched_action_def = weak_valid_sched_action_2_def

abbreviation weak_valid_sched_action_except_2 where
  "weak_valid_sched_action_except_2 thread \<equiv> weak_valid_sched_action_2 {thread}"

abbreviation weak_valid_sched_action_except :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
 "weak_valid_sched_action_except t s \<equiv>
    weak_valid_sched_action_2 {t} (cur_time s) (scheduler_action s) (release_queue s) (tcb_sts_of s)
                                  (tcb_scps_of s) (sc_refill_cfgs_of s)"

definition switch_in_cur_domain_2 where
  "switch_in_cur_domain_2 sa ekh cdom \<equiv>
    \<forall>t. sa = switch_thread t \<longrightarrow> in_cur_domain_2 t cdom ekh"

abbreviation switch_in_cur_domain:: "'z state \<Rightarrow> bool" where
  "switch_in_cur_domain s \<equiv> switch_in_cur_domain_2 (scheduler_action s) (etcbs_of s) (cur_domain s)"

lemmas switch_in_cur_domain_def = switch_in_cur_domain_2_def

abbreviation valid_sched_action_extras_2 where
  "valid_sched_action_extras_2 sa ct cdom etcbs tcb_sts \<equiv>
    is_activatable_2 ct sa tcb_sts \<and> switch_in_cur_domain_2 sa etcbs cdom"

abbreviation valid_sched_action_extras where
  "valid_sched_action_extras s
   \<equiv> valid_sched_action_extras_2 (scheduler_action s) (cur_thread s) (cur_domain s)
                                  (etcbs_of s) (tcb_sts_of s)"

definition valid_sched_action_2 where
  "valid_sched_action_2 wk_vsa except curtime sa ct cdom rlq etcbs tcb_sts tcb_scps sc_refill_cfgs \<equiv>
    (wk_vsa \<longrightarrow> weak_valid_sched_action_2 except curtime sa rlq tcb_sts tcb_scps sc_refill_cfgs)
    \<and> valid_sched_action_extras_2 sa ct cdom etcbs tcb_sts"

abbreviation valid_sched_action :: "'z state \<Rightarrow> bool" where
  "valid_sched_action s \<equiv>
    valid_sched_action_2 True {} (cur_time s) (scheduler_action s) (cur_thread s) (cur_domain s) (release_queue s)
                                 (etcbs_of s) (tcb_sts_of s) (tcb_scps_of s) (sc_refill_cfgs_of s)"

lemmas valid_sched_action_def = valid_sched_action_2_def

abbreviation ct_not_queued where
  "ct_not_queued s \<equiv> not_queued (cur_thread s) s"

abbreviation ct_not_in_release_q where
  "ct_not_in_release_q s \<equiv> not_in_release_q (cur_thread s) s"

definition
  "ct_not_in_q_2 queues sa ct \<equiv> sa = resume_cur_thread \<longrightarrow> not_queued_2 queues ct"

abbreviation ct_not_in_q :: "'z state \<Rightarrow> bool" where
  "ct_not_in_q s \<equiv> ct_not_in_q_2 (ready_queues s) (scheduler_action s) (cur_thread s)"

lemmas ct_not_in_q_def = ct_not_in_q_2_def

(* FIXME RT: This is currently the invariant required to show that do_reply_transfer
             can satisfy the preconditions of the scheduler.
             This could likely be strengthened to show that any live scheduling context
             is active. Such knowledge might allow us to safely remove many checks for
             active scheduling contexts in the C kernel. *)
definition active_if_reply_sc_at_2 ::
  "(obj_ref \<Rightarrow> obj_ref list option) \<Rightarrow> (obj_ref \<Rightarrow> sc_refill_cfg option) \<Rightarrow> obj_ref \<Rightarrow> bool"
  where
  "active_if_reply_sc_at_2 sc_reps sc_refill_cfgs scp
   \<equiv> pred_map (\<lambda>rs. rs \<noteq> []) sc_reps scp \<longrightarrow> pred_map active_scrc sc_refill_cfgs scp"

abbreviation non_empty_sc_replies_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "non_empty_sc_replies_at scp s \<equiv> pred_map (\<lambda>rs. rs \<noteq> []) (sc_replies_of s) scp"

abbreviation active_if_reply_sc_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "active_if_reply_sc_at scp s \<equiv> active_if_reply_sc_at_2 (sc_replies_of s) (sc_refill_cfgs_of s) scp"

definition active_reply_scs_2 ::
  "(obj_ref \<Rightarrow> obj_ref list option) \<Rightarrow> (obj_ref \<Rightarrow> sc_refill_cfg option) \<Rightarrow> bool"
  where
  "active_reply_scs_2 sc_reps sc_refill_cfgs
   \<equiv> \<forall>scp. active_if_reply_sc_at_2 sc_reps sc_refill_cfgs scp"

abbreviation active_reply_scs :: "'z::state_ext state \<Rightarrow> bool" where
  "active_reply_scs s \<equiv> active_reply_scs_2 (sc_replies_of s) (sc_refill_cfgs_of s)"

lemmas active_if_reply_sc_at_def = active_if_reply_sc_at_2_def
lemmas active_reply_scs_def = active_reply_scs_2_def
lemmas active_reply_scs_defs = active_if_reply_sc_at_def active_reply_scs_def

lemma active_reply_scsE:
  assumes "active_reply_scs_2 replies refill_cfgs"
  assumes "\<And>scp. pred_map (\<lambda>rs. rs \<noteq> []) replies' scp
                 \<longrightarrow> (pred_map (\<lambda>rs. rs \<noteq> []) replies scp \<longrightarrow> pred_map active_scrc refill_cfgs scp)
                 \<longrightarrow> pred_map active_scrc refill_cfgs' scp"
  shows "active_reply_scs_2 replies' refill_cfgs'"
  using assms by (simp add: active_reply_scs_2_def active_if_reply_sc_at_2_def)

definition valid_sched_2 where
  "valid_sched_2 wk_vsa vbl riq ctime cdom ct it queues rlq sa etcbs tcb_sts tcb_scps tcb_faults sc_refill_cfgs sc_reps \<equiv>
    valid_ready_qs_2 queues ctime etcbs tcb_sts tcb_scps sc_refill_cfgs
    \<and> valid_release_q_2 rlq tcb_sts tcb_scps sc_refill_cfgs
    \<and> ready_or_release_2 queues rlq
    \<and> ct_not_in_q_2 queues sa ct
    \<and> valid_sched_action_2 wk_vsa {} ctime sa ct cdom rlq etcbs tcb_sts tcb_scps sc_refill_cfgs
    \<and> ct_in_cur_domain_2 ct it sa cdom etcbs
    \<and> (vbl \<longrightarrow> valid_blocked_2 queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs)
    \<and> valid_idle_etcb_2 etcbs
    \<and> (riq \<longrightarrow> released_ipc_queues_2 ctime tcb_sts tcb_scps tcb_faults sc_refill_cfgs)
    \<and> active_reply_scs_2 sc_reps sc_refill_cfgs
    \<and> active_sc_valid_refills_2 ctime sc_refill_cfgs"

abbreviation valid_sched :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_sched \<equiv> valid_sched_pred (valid_sched_2 True True True)"

lemmas valid_sched_def = valid_sched_2_def

abbreviation "valid_sched_except_blocked_2 \<equiv> valid_sched_2 True False True"

abbreviation valid_sched_except_blocked :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_sched_except_blocked \<equiv> valid_sched_pred valid_sched_except_blocked_2"

lemma valid_sched_valid_sched_except_blocked:
  "valid_sched s \<longleftrightarrow> valid_blocked s \<and> valid_sched_except_blocked s"
  by (auto simp add: valid_sched_def)

lemma valid_sched_valid_sched_except_blocked_lift:
  assumes "\<lbrace>\<lambda>s. valid_sched_except_blocked s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_sched_except_blocked\<rbrace>"
  assumes "\<lbrace>\<lambda>s. valid_blocked s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_sched s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  unfolding valid_sched_valid_sched_except_blocked
  by (rule hoare_vcg_conj_lift_N_pre_conj[where N="\<lambda>P. P"]; rule assms)

abbreviation valid_sched_except_blocked_except_wk_sched_action_2 where
  "valid_sched_except_blocked_except_wk_sched_action_2 \<equiv> valid_sched_2 False False True"

abbreviation valid_sched_except_blocked_except_wk_sched_action :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_sched_except_blocked_except_wk_sched_action
   \<equiv> valid_sched_pred valid_sched_except_blocked_except_wk_sched_action_2"

abbreviation "valid_sched_except_blocked_except_released_ipc_qs_2 \<equiv> valid_sched_2 True False False"

abbreviation valid_sched_except_blocked_except_released_ipc_qs :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_sched_except_blocked_except_released_ipc_qs
   \<equiv> valid_sched_pred valid_sched_except_blocked_except_released_ipc_qs_2"

abbreviation einvs :: "det_ext state \<Rightarrow> bool" where
  "einvs \<equiv> invs and valid_list and valid_sched"


definition not_cur_thread_2 :: "obj_ref \<Rightarrow> scheduler_action \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "not_cur_thread_2 thread sa ct \<equiv> sa = resume_cur_thread \<longrightarrow> thread \<noteq> ct"

abbreviation not_cur_thread :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "not_cur_thread thread s \<equiv> not_cur_thread_2 thread (scheduler_action s) (cur_thread s)"

lemmas not_cur_thread_def = not_cur_thread_2_def

definition simple_sched_action_2 :: "scheduler_action \<Rightarrow> bool" where
  "simple_sched_action_2 action \<equiv> (case action of switch_thread t \<Rightarrow> False | _ \<Rightarrow> True)"

abbreviation simple_sched_action :: "'z state \<Rightarrow> bool" where
  "simple_sched_action s \<equiv> simple_sched_action_2 (scheduler_action s)"

lemmas simple_sched_action_def = simple_sched_action_2_def

definition schact_is_rct_2 :: "scheduler_action \<Rightarrow> bool" where
  "schact_is_rct_2 schact \<equiv> schact = resume_cur_thread"

abbreviation schact_is_rct :: "'z state \<Rightarrow> bool" where
  "schact_is_rct s \<equiv> schact_is_rct_2 (scheduler_action s)"

lemmas schact_is_rct_def = schact_is_rct_2_def

lemma schact_is_rct[elim!]: "schact_is_rct s \<Longrightarrow> scheduler_action s = resume_cur_thread"
  apply (simp add: schact_is_rct_def)
  done

lemma schact_is_rct_simple[elim!]: "schact_is_rct s \<Longrightarrow> simple_sched_action s"
  apply (simp add: simple_sched_action_def schact_is_rct_def)
  done

definition scheduler_act_not_2 where
"scheduler_act_not_2 sa t \<equiv> sa \<noteq> switch_thread t"


abbreviation scheduler_act_not :: "obj_ref \<Rightarrow> 'z state  \<Rightarrow> bool" where
"scheduler_act_not t s \<equiv> scheduler_act_not_2 (scheduler_action s) t"

abbreviation scheduler_act_sane :: "'z state \<Rightarrow> bool" where
"scheduler_act_sane s \<equiv> scheduler_act_not_2 (scheduler_action s) (cur_thread s)"

lemmas scheduler_act_sane_def = scheduler_act_not_2_def
lemmas scheduler_act_not_def = scheduler_act_not_2_def

(* ct_in_state' *)
abbreviation ct_in_state' :: "_ \<Rightarrow> 'z state \<Rightarrow> bool" where
  "ct_in_state' P s \<equiv> pred_map P (tcb_sts_of s) (cur_thread s)"

(* next_thread *)
definition next_thread where
  "next_thread queues \<equiv> (hd (max_non_empty_queue queues))"

lemma valid_blocked_except_set_2_subset[elim]:
  "valid_blocked_except_set_2 T queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs \<Longrightarrow>
   T \<subseteq> S \<Longrightarrow>
   valid_blocked_except_set_2 S queues rlq sa ct tcb_sts tcb_scps sc_refill_cfgs"
  by (fastforce simp: valid_blocked_defs)

lemmas valid_blocked_except_set_2_subset_safe[elim!, simp] =
  valid_blocked_except_set_2_subset[where T="{}", simplified]
  valid_blocked_except_set_2_subset[OF _ subset_insertI]

lemma valid_blocked_except_set_cur_thread[simp]:
  "valid_blocked_except_set (insert (cur_thread s) S) s = valid_blocked_except_set S s"
   by (auto simp: valid_blocked_defs)

lemma valid_blocked_except_set_not_runnable:
  "valid_blocked_except_set {t} s \<Longrightarrow> st_tcb_at (\<lambda>st. \<not> runnable st) t s  \<Longrightarrow> valid_blocked s"
  unfolding valid_blocked_defs obj_at_kh_kheap_simps runnable_eq
  by (erule allEI; rename_tac t'; case_tac "t' = t"; clarsimp simp: pred_map_simps)

lemma valid_sched_valid_blocked[elim!]:
  "valid_sched s \<Longrightarrow> valid_blocked_except_set S s" by (clarsimp simp: valid_sched_def)

lemma valid_sched_valid_ready_qs[elim!]:
  "valid_sched s \<Longrightarrow> valid_ready_qs s" by (clarsimp simp: valid_sched_def)

lemma valid_sched_valid_release_q[elim!]:
  "valid_sched s \<Longrightarrow> valid_release_q s" by (clarsimp simp: valid_sched_def)

lemma valid_sched_ready_or_release[elim!]:
  "valid_sched s \<Longrightarrow> ready_or_release s" by (clarsimp simp: valid_sched_def)

lemma valid_sched_valid_sched_action[elim!]:
  "valid_sched s \<Longrightarrow> valid_sched_action s" by (simp add: valid_sched_def)

lemma valid_sched_weak_valid_sched_action[elim!]:
  "valid_sched s \<Longrightarrow> weak_valid_sched_action s" by (simp add: valid_sched_def valid_sched_action_def)

lemma valid_sched_ct_in_cur_domain[elim!]:
  "valid_sched s \<Longrightarrow> ct_in_cur_domain s" by (simp add: valid_sched_def)

lemma valid_sched_released_ipc_queues[elim!]:
  "valid_sched s \<Longrightarrow> released_ipc_queues s"
  by (clarsimp simp: valid_sched_def)

lemma valid_sched_active_sc_valid_refills[elim!]:
  "valid_sched s \<Longrightarrow> active_sc_valid_refills s" by (simp add: valid_sched_def)

lemma valid_sched_imp_except_blocked[elim!]:
  "valid_sched s \<Longrightarrow> valid_sched_except_blocked s"
  by (clarsimp simp: valid_sched_def)

(* sched_context and other thread properties *)
abbreviation sc_with_tcb_prop ::
  "obj_ref \<Rightarrow> (obj_ref \<Rightarrow> 'z state \<Rightarrow> bool) \<Rightarrow> 'z state \<Rightarrow> bool"
  where
  "sc_with_tcb_prop scp P s \<equiv> \<forall>t. heap_ref_eq scp t (tcb_scps_of s) \<longrightarrow> P t s"

abbreviation sc_not_in_release_q :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "sc_not_in_release_q scp s \<equiv> sc_with_tcb_prop scp not_in_release_q s"

abbreviation release_q_not_linked :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "release_q_not_linked scp s \<equiv> \<forall>t\<in>set (release_queue s). pred_map (\<lambda>p. p \<noteq> Some scp) (tcb_scps_of s) t"

lemma sc_not_in_release_q_imp_not_linked:
  "\<lbrakk>valid_release_q s; sc_not_in_release_q scp s\<rbrakk> \<Longrightarrow> release_q_not_linked scp s"
  by (fastforce simp:  not_in_release_q_def valid_release_q_def vs_all_heap_simps)

abbreviation sc_not_in_ready_q :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "sc_not_in_ready_q scp s \<equiv> sc_with_tcb_prop scp not_queued s"

abbreviation sc_scheduler_act_not :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "sc_scheduler_act_not scp s \<equiv> sc_with_tcb_prop scp scheduler_act_not s"

abbreviation ipc_queued_thread :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "ipc_queued_thread t s \<equiv> pred_map ipc_queued_thread_state (tcb_sts_of s) t"

lemma released_ipc_queues_blocked_on_recv_ntfn_E1:
  "released_ipc_queues s \<Longrightarrow> blocked_on_recv_ntfn_tcb_at t s \<Longrightarrow> released_if_bound_sc_tcb_at t s"
  by (clarsimp simp: released_ipc_queues_defs)

lemma released_ipc_queues_blocked_on_send_E1:
  "released_ipc_queues s \<Longrightarrow> blocked_on_send_tcb_at t s \<Longrightarrow> valid_sender_sc_tcb_at t s"
  by (clarsimp simp: released_ipc_queues_defs)

lemma released_ipc_queues_blocked_on_reply_E1:
  "released_ipc_queues s \<Longrightarrow> blocked_on_reply_tcb_at t s \<Longrightarrow> active_if_bound_sc_tcb_at t s"
  by (clarsimp simp: released_ipc_queues_defs)

abbreviation not_ipc_queued_thread :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "not_ipc_queued_thread t s \<equiv> \<not> ipc_queued_thread t s"

abbreviation sc_not_in_ep_q :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "sc_not_in_ep_q scp s \<equiv> sc_with_tcb_prop scp not_ipc_queued_thread s"

lemma valid_sched_not_runnable_not_queued:
  "\<lbrakk>valid_sched s; \<not> pred_map runnable (tcb_sts_of s) tptr\<rbrakk> \<Longrightarrow> not_queued tptr s"
  by (clarsimp simp: valid_sched_def valid_ready_qs_def not_queued_def)

lemma valid_sched_not_runnable_not_in_release_q:
  "\<lbrakk>valid_sched s; \<not> pred_map runnable (tcb_sts_of s) tptr\<rbrakk> \<Longrightarrow> not_in_release_q tptr s"
  by (clarsimp simp: valid_sched_def valid_release_q_def not_in_release_q_def)

lemma valid_sched_no_active_sc_not_queued:
  "\<lbrakk>valid_sched s; \<not> active_sc_tcb_at tptr s\<rbrakk> \<Longrightarrow> not_queued tptr s"
  by (clarsimp simp: valid_sched_def valid_ready_qs_def not_queued_def released_sc_tcb_at_def)

lemma valid_sched_no_active_sc_not_in_release_q:
  "\<lbrakk>valid_sched s; \<not> active_sc_tcb_at tptr s\<rbrakk> \<Longrightarrow> not_in_release_q tptr s"
  by (clarsimp simp: valid_sched_def valid_release_q_def not_in_release_q_def released_sc_tcb_at_def)

lemma valid_sched_not_runnable_scheduler_act_not:
  "\<lbrakk>valid_sched s; \<not> pred_map runnable (tcb_sts_of s) tptr\<rbrakk> \<Longrightarrow> scheduler_act_not tptr s"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                     scheduler_act_not_def)

lemma valid_sched_no_active_sc_scheduler_act_not:
  "\<lbrakk>valid_sched s; \<not> active_sc_tcb_at tptr s\<rbrakk> \<Longrightarrow> scheduler_act_not tptr s"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                     scheduler_act_not_def released_sc_tcb_at_def)

lemma valid_sched_in_release_q_scheduler_act_not:
  "\<lbrakk>valid_sched s; in_release_queue tptr s\<rbrakk> \<Longrightarrow> scheduler_act_not tptr s"
  by (clarsimp simp: valid_sched_def valid_sched_action_def weak_valid_sched_action_def
                     scheduler_act_not_def in_release_queue_def)

(*********)

lemma sc_with_tcb_prop_rev:
  "\<lbrakk>ko_at (SchedContext sc n) scp s; sc_tcb sc = Some tp; sc_with_tcb_prop scp P s; invs s\<rbrakk>
   \<Longrightarrow> P tp s"
  by (fastforce simp: obj_at_def vs_all_heap_simps dest!: invs_sym_refs sym_ref_sc_tcb)

lemma sc_with_tcb_prop_rev':
  "\<lbrakk>sc_tcb_sc_at ((=) (Some tp)) scp s; sc_with_tcb_prop scp P s; invs s\<rbrakk>
   \<Longrightarrow> P tp s"
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def)
  apply (drule sym[where t="sc_tcb _"])
  by (rule sc_with_tcb_prop_rev, clarsimp simp: pred_tcb_at_def obj_at_def)

(* FIXME: move *)
lemma ko_opt_cases:
  assumes "kh p = None \<Longrightarrow> P"
  assumes "\<And>n cnode. kh p = Some (CNode n cnode) \<Longrightarrow> P"
  assumes "\<And>tcb. kh p = Some (TCB tcb) \<Longrightarrow> P"
  assumes "\<And>ep. kh p = Some (Endpoint ep) \<Longrightarrow> P"
  assumes "\<And>ntfn. kh p = Some (Notification ntfn) \<Longrightarrow> P"
  assumes "\<And>sc n. kh p = Some (SchedContext sc n) \<Longrightarrow> P"
  assumes "\<And>reply. kh p = Some (Reply reply) \<Longrightarrow> P"
  assumes "\<And>aobj. kh p = Some (ArchObj aobj) \<Longrightarrow> P"
  shows P
  apply (cases "kh p", erule assms)
  by (rename_tac ko; case_tac ko; clarsimp elim!: assms)

lemma tcb_ready_times_of_kh_update_indep[simp]:
  assumes "\<And>tcb sc n. {Some (TCB tcb), Some (SchedContext sc n)} \<inter> {kh ref, Some new} = {}"
  shows "tcb_ready_times_of_kh (kh(ref \<mapsto> new)) = tcb_ready_times_of_kh kh"
  using assms
  apply (clarsimp simp: fun_upd_def vs_all_heap_simps)
  by (cases new; rule ko_opt_cases[where kh=kh and p=ref]; fastforce simp: vs_all_heap_simps)

lemmas tcb_ready_times_of_kh_update_indep'[simp]
  = tcb_ready_times_of_kh_update_indep[simplified fun_upd_def]

lemma tcb_ready_time_ep_update:
  "\<lbrakk> ep_at ref s; a_type new = AEndpoint\<rbrakk> \<Longrightarrow>
   tcb_ready_times_of_kh (kheap s(ref \<mapsto> new)) = tcb_ready_times_of s"
  by (clarsimp simp: obj_at_def is_ep)

lemma tcb_ready_time_reply_update:
  "\<lbrakk> reply_at ref s; a_type new = AReply\<rbrakk> \<Longrightarrow>
   tcb_ready_times_of_kh (kheap s(ref \<mapsto> new)) = tcb_ready_times_of s"
  by (clarsimp simp: obj_at_def is_reply)

lemma tcb_ready_time_ntfn_update:
  "\<lbrakk> ntfn_at ref s; a_type new = ANTFN\<rbrakk> \<Longrightarrow>
   tcb_ready_times_of_kh (kheap s(ref \<mapsto> new)) = tcb_ready_times_of s"
  by (clarsimp simp: obj_at_def is_ntfn)

lemmas tcb_ready_time_update_indeps[simp]
  = tcb_ready_time_ep_update tcb_ready_time_reply_update tcb_ready_time_ntfn_update

lemmas tcb_ready_time_update_indeps'[simp]
  = tcb_ready_time_update_indeps[unfolded fun_upd_def]

lemma tcb_ready_time_thread_state_update[simp]:
  assumes "kheap s tp = Some (TCB tcb)"
  assumes "tcb_sched_context tcb' = tcb_sched_context tcb"
  shows "tcb_ready_times_of_kh (kheap s(tp \<mapsto> TCB tcb')) = tcb_ready_times_of s"
  using assms by (simp add: fun_upd_def vs_all_heap_simps)

lemmas tcb_ready_time_thread_state_update'[simp]
  = tcb_ready_time_thread_state_update[unfolded fun_upd_def]

lemma tcb_ready_time_kh_tcb_sc_update:
  "\<lbrakk>kheap s tp = Some (TCB tcb);
    tcb_sched_context tcb = Some scp; kheap s scp = Some (SchedContext sc n);
    scopt = Some scp'; kheap s scp' = Some (SchedContext sc' n');
    r_time (refill_hd sc) = r_time (refill_hd sc') \<rbrakk> \<Longrightarrow>
   tcb_ready_times_of_kh
            (kheap s(tp \<mapsto> TCB (tcb\<lparr>tcb_sched_context := scopt\<rparr>)))
        = tcb_ready_times_of s"
  by (auto intro!: map_eqI
             simp: fun_upd_def vs_all_heap_simps tcb_ready_times_defs
                   map_project_simps opt_map_simps map_join_simps
            split: if_splits)

lemma tcb_at_simple_type_update[iff]:
  "\<lbrakk>obj_at is_simple_type epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
      tcbs_of_kh (kheap s(epptr \<mapsto> ko)) = tcbs_of s"
  by (rule map_eqI, auto simp add: vs_heap_simps obj_at_def)

lemma sc_at_simple_type_update[iff]:
  "\<lbrakk>obj_at is_simple_type epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
      scs_of_kh (kheap s(epptr \<mapsto> ko)) = scs_of s"
  by (rule map_eqI, auto simp add: vs_heap_simps obj_at_def)

(* lifting lemmas *)

(* FIXME move *)
lemma sorted_wrt_cmp_lift:
  assumes "\<And>x y. \<lbrace>\<lambda>s. N (P s x y) \<and> R s \<rbrace> f \<lbrace>\<lambda>rv s. N (P s x y)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (sorted_wrt (P s) xs) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sorted_wrt (P s) xs)\<rbrace>"
proof (induct xs)
  case (Cons x xs) show ?case
    by (wpsimp wp: hoare_vcg_conj_lift_N_pre_conj[where N=N, OF _ Cons]
                   hoare_vcg_ball_lift_N_pre_conj[where N=N] assms)
qed wpsimp

lemmas ct_not_queued_lift = hoare_lift_Pf2[where f="cur_thread" and P="not_queued"]
lemmas ct_not_in_release_q_lift = hoare_lift_Pf2[where f="cur_thread" and P="not_in_release_q"]
lemmas sch_act_sane_lift = hoare_lift_Pf2[where f="cur_thread" and P="scheduler_act_not"]

lemma valid_ready_qs_lift_pre_conj:
  assumes a: "\<And>t. \<lbrace>\<lambda>s. pred_map runnable (tcb_sts_of s) t \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. pred_map runnable (tcb_sts_of s) t\<rbrace>"
  assumes b: "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
  assumes c: "\<And>t. \<lbrace>\<lambda>s. budget_ready t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_ready t s\<rbrace>"
  assumes d: "\<And>t. \<lbrace>\<lambda>s. budget_sufficient t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_sufficient t s\<rbrace>"
  assumes e: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
  assumes r: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_ready_qs s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply (simp add: valid_ready_qs_def)
  apply wp_pre
   apply (rule hoare_lift_Pf_pre_conj[where f=ready_queues, OF _ r])
   by (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift
                  valid_sched_pred_heap_proj_lifts[where N="\<lambda>P. P"]
                  released_sc_tcb_at_lift a b c d e)+

lemmas valid_ready_qs_lift = valid_ready_qs_lift_pre_conj[where R = \<top>, simplified]

lemma sorted_wrt_img_ord_eq_lift:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f' x = f x"
  shows "sorted_wrt (img_ord f' op) xs = sorted_wrt (img_ord f op) xs"
  using assms by (induct xs) (auto simp: img_ord_def)

lemma sorted_wrt_img_ord_valid_lift:
  assumes "\<And>x Q. x \<in> set xs \<Longrightarrow> \<lbrace>\<lambda>s. Q (P s x) \<and> R s \<rbrace> f \<lbrace>\<lambda>rv s. Q (P s x)\<rbrace>"
  shows "\<lbrace>\<lambda>s. N (sorted_wrt (img_ord (P s) op) xs) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sorted_wrt (img_ord (P s) op) xs)\<rbrace>"
  by (rule validI, auto elim!: rsubst[of N] use_valid_inv intro!: sorted_wrt_img_ord_eq_lift assms)

lemma sorted_release_q_2_eq_lift:
  assumes "\<And>t. t \<in> set queue \<Longrightarrow> sc_ready_times_2 heap' t = sc_ready_times_2 heap t"
  shows "sorted_release_q_2 heap' queue = sorted_release_q_2 heap queue"
  by (clarsimp simp: sorted_release_q_2_def intro!: sorted_wrt_img_ord_eq_lift assms)

lemmas sorted_release_qE = sorted_release_q_2_eq_lift[THEN iffD2, rotated]

(* FIXME: move *)
lemma opt_eq_iff:
  "opt' = opt \<longleftrightarrow> (opt' = None \<longleftrightarrow> opt = None) \<and> (\<forall>x. opt' = Some x \<longleftrightarrow> opt = Some x)"
  by blast

\<comment> \<open>This makes the equality accessible to heap simplification rules, without creating a loop.\<close>
lemmas sc_ready_time_eq_iff'
  = opt_eq_iff[where opt'="sc_ready_times_2 _ _" and opt="sc_ready_times_2 _ _"]

lemma sc_ready_time_eq_iff:
  "sc_ready_times_2 heap' t' = sc_ready_times_2 heap t
   \<longleftrightarrow> (heap' t' = None \<longleftrightarrow> heap t = None)
        \<and> (\<forall>rt. map_project sc_ready_time heap' t' = Some rt
                 \<longleftrightarrow> map_project sc_ready_time heap t = Some rt)"
  unfolding sc_ready_time_eq_iff'
  by (auto simp: sc_ready_times_2_def map_project_simps)

lemma sorted_release_q_2_valid_lift:
  assumes r: "\<And>P t. t \<in> set queue \<Longrightarrow> \<lbrace>\<lambda>s. P (sc_ready_times_2 (heap s) t) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (sc_ready_times_2 (heap s) t)\<rbrace>"
  shows "\<lbrace>\<lambda>s. sorted_release_q_2 (heap s) queue \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. sorted_release_q_2 (heap s) queue\<rbrace>"
  by (clarsimp simp: sorted_release_q_2_def intro!: sorted_wrt_img_ord_valid_lift elim!: assms)

lemma sorted_release_q_lift:
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
  assumes r: "\<And>P. \<lbrace>\<lambda>s. P (tcb_ready_times_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (tcb_ready_times_of s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. sorted_release_q s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. sorted_release_q\<rbrace>"
  by (wpsimp simp: sorted_release_q_def wp: hoare_lift_Pf_pre_conj[where f="\<lambda>s. release_queue s", OF r c])

lemma valid_release_q_lift_pre_conj:
  assumes "\<And>P t. \<lbrace>\<lambda>s. pred_map P (tcb_sts_of s) t \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. pred_map P (tcb_sts_of s) t\<rbrace>"
  assumes a': "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
      and f: "\<And>P. \<lbrace>\<lambda>s. P (tcb_ready_times_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (tcb_ready_times_of s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. (valid_release_q s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  unfolding valid_release_q_def sorted_release_q_def
  apply wp_pre
   apply (rule hoare_lift_Pf_pre_conj[where f=release_queue, OF _ c])
   by (wpsimp wp: hoare_vcg_ball_lift valid_sched_pred_heap_proj_lifts[where N="\<lambda>P. P"] assms)+

lemmas valid_release_q_lift = valid_release_q_lift_pre_conj[where R = \<top>, simplified]

lemma valid_blocked_lift_pre_conj:
  assumes a: "\<And>t. \<lbrace>\<lambda>s. \<not> pred_map active (tcb_sts_of s) t \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> pred_map active (tcb_sts_of s) t\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and f: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
      and b: "\<And>t. \<lbrace>\<lambda>s. \<not> active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> active_sc_tcb_at t s\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_blocked_except_set S s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  apply wp_pre
   apply (rule hoare_lift_Pf_pre_conj[where f=scheduler_action, OF _ c])
   apply (rule hoare_lift_Pf_pre_conj[where f=ready_queues, OF _ d])
   apply (rule hoare_lift_Pf_pre_conj[where f=cur_thread, OF _ e])
   apply (rule hoare_lift_Pf_pre_conj[where f=release_queue, OF _ f])
   unfolding valid_blocked_defs
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift a b)
  by clarsimp

lemmas valid_blocked_lift = valid_blocked_lift_pre_conj[where R=\<top>, simplified]

lemma ct_not_in_q_lift_pre_conj:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. ct_not_in_q s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. ct_not_in_q\<rbrace>"
  apply wp_pre
   apply (rule hoare_lift_Pf_pre_conj[where f=scheduler_action, OF _ a])
   apply (rule hoare_lift_Pf_pre_conj[where f=ready_queues, OF _ b])
   apply (rule hoare_lift_Pf_pre_conj[where f=cur_thread, OF _ c])
   by wpsimp+

lemmas ct_not_in_q_lift = ct_not_in_q_lift_pre_conj[where R=\<top>, simplified]

lemma ct_in_cur_domain_lift_pre_conj:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. ct_in_cur_domain s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply wp_pre
   apply (rule hoare_lift_Pf_pre_conj[where f=etcbs_of, OF _ a])
   apply (rule hoare_lift_Pf_pre_conj[where f=scheduler_action, OF _ b])
   apply (rule hoare_lift_Pf_pre_conj[where f=cur_domain, OF _ c])
   apply (rule hoare_lift_Pf_pre_conj[where f=cur_thread, OF _ d])
   apply (rule hoare_lift_Pf_pre_conj[where f=idle_thread, OF _ e])
   by wpsimp+

lemmas ct_in_cur_domain_lift = ct_in_cur_domain_lift_pre_conj[where R=\<top>, simplified]

lemma weak_valid_sched_action_lift_pre_conj:
  assumes ts: "\<And>t. \<lbrace>\<lambda>s. pred_map runnable (tcb_sts_of s) t \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. pred_map runnable (tcb_sts_of s) t\<rbrace>"
              "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
              "\<And>t. \<lbrace>\<lambda>s. budget_ready t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_ready t s\<rbrace>"
              "\<And>t. \<lbrace>\<lambda>s. budget_sufficient t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_sufficient t s\<rbrace>"
  assumes sa: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes rq: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. weak_valid_sched_action s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply wp_pre
   apply (rule hoare_lift_Pf_pre_conj[where f=scheduler_action, OF _ sa])
   apply (rule hoare_lift_Pf_pre_conj[where f=release_queue, OF _ rq])
   unfolding weak_valid_sched_action_def
   by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift ts released_sc_tcb_at_lift)+

lemmas weak_valid_sched_action_lift = weak_valid_sched_action_lift_pre_conj[where R = \<top>, simplified]

lemma switch_in_cur_domain_lift_pre_conj:
  assumes a: "\<And>P t. \<lbrace>\<lambda>s. etcb_at P t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at P t s\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. switch_in_cur_domain s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. switch_in_cur_domain\<rbrace>"
  apply wp_pre
   apply (rule hoare_lift_Pf_pre_conj[where f=scheduler_action, OF _ b])
   apply (rule hoare_lift_Pf_pre_conj[where f=cur_domain, OF _ c])
   by (wpsimp simp: switch_in_cur_domain_def in_cur_domain_def wp: hoare_vcg_all_lift static_imp_wp a)+

lemmas switch_in_cur_domain_lift = switch_in_cur_domain_lift_pre_conj[where R = \<top>, simplified]

lemma valid_sched_action_lift_pre_conj:
  assumes ts: "\<And>Q t. \<lbrace>\<lambda>s. pred_map Q (tcb_sts_of s) t \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. pred_map Q (tcb_sts_of s) t\<rbrace>"
              "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
              "\<And>t. \<lbrace>\<lambda>s. budget_ready t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_ready t s\<rbrace>"
              "\<And>t. \<lbrace>\<lambda>s. budget_sufficient t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_sufficient t s\<rbrace>"
              "\<And>P t. \<lbrace>\<lambda>s. etcb_at P t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at P t s\<rbrace>"
  assumes ct: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes sa: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes cd: "\<And>Q. \<lbrace>\<lambda>s. Q (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q (cur_domain s)\<rbrace>"
  assumes rq: "\<And>Q. \<lbrace>\<lambda>s. Q (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q (release_queue s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_sched_action s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply wp_pre
   apply (rule hoare_lift_Pf_pre_conj[where f=cur_thread, OF _ ct])
   unfolding valid_sched_action_def is_activatable_def
   by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift
                  switch_in_cur_domain_lift_pre_conj weak_valid_sched_action_lift_pre_conj
                  ts sa cd rq)+

lemmas valid_sched_action_lift = valid_sched_action_lift_pre_conj[where R = \<top>, simplified]

lemma valid_idle_etcb_lift_pre_conj:
  assumes d: "\<And>P t. \<lbrace>\<lambda>s. etcb_at P t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at P t s\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_idle_etcb s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_idle_etcb\<rbrace>"
  by (wpsimp wp: d simp: valid_idle_etcb_def)

lemmas valid_idle_etcb_lift[wp] = valid_idle_etcb_lift_pre_conj[where R = \<top>, simplified]

lemma active_reply_scs_lift_pre_conj:
  assumes "\<And>scp. \<lbrace>\<lambda>s. active_if_reply_sc_at scp s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_if_reply_sc_at scp s\<rbrace>"
  shows "\<lbrace>\<lambda>s. active_reply_scs s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_reply_scs s\<rbrace>"
  unfolding active_reply_scs_2_def by (intro hoare_vcg_all_lift_N_pre_conj assms)

lemma valid_sched_lift_pre_conj:
  assumes "\<And>N P t. \<lbrace>\<lambda>s. N (pred_map P (tcb_sts_of s) t) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (pred_map P (tcb_sts_of s) t)\<rbrace>"
  assumes "\<And>P t. \<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) t \<and> R s\<rbrace>
               f \<lbrace>\<lambda>rv s. \<not> pred_map active_scrc (sc_refill_cfgs_of s) t\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. valid_refills t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. valid_refills t s\<rbrace>"
  assumes "\<And>scp. \<lbrace>\<lambda>s. bounded_release_time scp s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. bounded_release_time scp s\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. budget_ready t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_ready t s\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. budget_sufficient t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_sufficient t s\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (tcb_ready_times_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (tcb_ready_times_of s)\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. pred_map_eq None (tcb_scps_of s) t \<and> R s\<rbrace> f \<lbrace>\<lambda>rf s. pred_map_eq None (tcb_scps_of s) t\<rbrace>"
  assumes "\<And>t. \<lbrace>\<lambda>s. timeout_faulted_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. timeout_faulted_tcb_at t s\<rbrace>"
  assumes "\<And>scp. \<lbrace>\<lambda>s. active_if_reply_sc_at scp s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_if_reply_sc_at scp s\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_sched s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  by (wpsimp simp: valid_sched_def ready_or_release_def ready_or_release_def
               wp: valid_ready_qs_lift_pre_conj ct_not_in_q_lift_pre_conj
                   ct_in_cur_domain_lift_pre_conj valid_release_q_lift_pre_conj
                   valid_sched_action_lift_pre_conj valid_blocked_lift_pre_conj assms
                   released_ipc_queues_lift_pre_conj active_sc_valid_refills_lift_pre_conj
                   active_reply_scs_lift_pre_conj hoare_vcg_all_lift hoare_vcg_imp_lift)

lemmas valid_sched_lift = valid_sched_lift_pre_conj[where R = \<top>, simplified]

(* This predicate declares that the current thread has a scheduling context that is
    active, ready and sufficient. *)
abbreviation ct_released where
  "ct_released s \<equiv> released_sc_tcb_at (cur_thread s) s"

lemma scheduler_act_sane_lift:
  assumes A: "\<And>P. f \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace>"
  assumes B: "\<And>P. f \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace>"
  shows " f \<lbrace>scheduler_act_sane\<rbrace>"
  using A B hoare_lift_Pf by fastforce

lemma valid_ready_qs_in_ready_qD:
  "valid_ready_qs s \<Longrightarrow>
   in_ready_q tcb_ptr s \<Longrightarrow>
   st_tcb_at runnable tcb_ptr s \<and>
   active_sc_tcb_at tcb_ptr s \<and>
   budget_sufficient tcb_ptr s \<and>
   budget_ready tcb_ptr s"
  by (clarsimp simp: released_sc_tcb_at_def valid_ready_qs_def in_ready_q_def
                     obj_at_kh_kheap_simps)

lemma invs_cur_sc_tcb_symref:
  "invs s \<Longrightarrow> schact_is_rct s \<Longrightarrow> bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (cur_thread s) s"
  apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl invs_sym_refs], simp)
  apply (simp add: invs_def cur_sc_tcb_def sc_at_pred_n_def obj_at_def schact_is_rct_def)
  done

lemma sym_refs_pred_map_eq_iff_sc_tcb_sc_at:
  assumes pre: "\<And>sc_opt. P sc_opt \<longleftrightarrow> sc_opt = Some sc"
               "\<And>t_opt. Q t_opt \<longleftrightarrow> t_opt = Some t"
  assumes sym: "sym_refs (state_refs_of s)"
  shows "pred_map P (tcb_scps_of s) t \<longleftrightarrow> sc_tcb_sc_at Q sc s"
  using sym by (fastforce simp: pred_tcb_at_def sc_tcb_sc_at_def obj_at_def pre tcb_at_kh_simps[symmetric]
                                sym_refs_def state_refs_of_def get_refs_def2 refs_of_rev
                         split: option.splits)

(*** cur_sc_chargeable ***)

definition cur_sc_chargeable_2 where
  "cur_sc_chargeable_2 cursc curthread tcb_sts tcb_scps \<equiv>
    (\<forall>scp. pred_map_eq (Some scp) tcb_scps (curthread) \<longrightarrow> scp = cursc) \<and>
    (\<forall>tp. pred_map_eq (Some cursc) tcb_scps tp \<longrightarrow> tp = curthread \<or> pred_map inactive tcb_sts tp)"

abbreviation cur_sc_chargeable :: "'z state \<Rightarrow> bool" where
"cur_sc_chargeable s \<equiv> cur_sc_chargeable_2 (cur_sc s) (cur_thread s) (tcb_sts_of s) (tcb_scps_of s) "

lemmas cur_sc_chargeable_def = cur_sc_chargeable_2_def

lemma cur_sc_chargeable_def2:
  "cur_sc_chargeable s
   \<equiv> (\<forall>scp. bound_sc_tcb_at (\<lambda>x. x = Some scp) (cur_thread s) s \<longrightarrow> scp = cur_sc s) \<and>
     (\<forall>x. bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s \<longrightarrow> (x = cur_thread s \<or> st_tcb_at inactive x s))"
  by (clarsimp simp: cur_sc_chargeable_def tcb_at_kh_simps vs_all_heap_simps)

lemma cur_sc_chargeable_lift_pre_conj:
  assumes A: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  assumes B: "\<And>P. \<lbrace>\<lambda>s. P (cur_sc s)\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_sc s)\<rbrace>"
  assumes C: "\<And>P t. \<lbrace>\<lambda>s. \<not> (bound_sc_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. \<not> (bound_sc_tcb_at P t s)\<rbrace>"
  assumes D: "\<And>P t. \<lbrace>\<lambda>s. (st_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. (st_tcb_at P t s)\<rbrace>"
  shows "\<lbrace>cur_sc_chargeable and R\<rbrace> f \<lbrace>\<lambda>_. cur_sc_chargeable\<rbrace>"
  unfolding cur_sc_chargeable_def2
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift C D hoare_vcg_disj_lift | wps A B)+

lemmas cur_sc_chargeable_lift = cur_sc_chargeable_lift_pre_conj[where R=\<top>, simplified]

lemma invs_cur_sc_chargeableE:
  "invs s \<Longrightarrow> schact_is_rct s \<Longrightarrow> cur_sc_chargeable s"
  apply (subgoal_tac "sc_tcb_sc_at (\<lambda>x. x = Some (cur_thread s)) (cur_sc s) s")
   apply (subgoal_tac "bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) (cur_thread s) s")
    apply (clarsimp simp: cur_sc_chargeable_def)
    apply (intro conjI)
     apply (clarsimp simp: tcb_at_kh_simps vs_all_heap_simps)
    apply (clarsimp simp: pred_map_eq_def)
     apply (subst (asm) sym_refs_pred_map_eq_iff_sc_tcb_sc_at[OF eq_commute refl invs_sym_refs], simp)+
     apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
   apply (subst sym_refs_bound_sc_tcb_iff_sc_tcb_sc_at[OF refl refl invs_sym_refs]; simp)
  apply (simp add: invs_def cur_sc_tcb_def sc_at_pred_n_def obj_at_def schact_is_rct_def)
  done

lemma schact_is_rct_sane[elim!]: "schact_is_rct s \<Longrightarrow> scheduler_act_sane s"
  apply (simp add: simple_sched_action_def schact_is_rct_def scheduler_act_not_def)
  done

\<comment> \<open>The current thread and current sc are bound (assuming sym_refs))\<close>

abbreviation cur_sc_tcb_are_bound :: "'z state \<Rightarrow> bool" where
  "cur_sc_tcb_are_bound s \<equiv> heap_ref_eq (cur_sc s) (cur_thread s) (tcb_scps_of s)"

abbreviation ct_not_blocked where
  "ct_not_blocked s \<equiv> ct_in_state (\<lambda>x. \<not>ipc_queued_thread_state x) s"

abbreviation ct_not_blocked_on_ntfn where
  "ct_not_blocked_on_ntfn s \<equiv> ct_in_state (\<lambda>x. \<not> is_blocked_on_ntfn x) s"

abbreviation ct_not_blocked_on_receive where
  "ct_not_blocked_on_receive s \<equiv> ct_in_state (\<lambda>x. \<not> is_blocked_on_receive x) s"

lemma ct_in_state_kh_simp:
  "ct_in_state P s = ct_in_state' P s"
  unfolding ct_in_state_def
  by (clarsimp simp: tcb_at_kh_simps)

\<comment> \<open>The current thread and current sc can only be bound to each other, symmetrically\<close>

definition cur_sc_tcb_only_sym_bound_2 where
  "cur_sc_tcb_only_sym_bound_2 cursc curthread tcb_scps \<equiv>
    (\<forall>scp. pred_map_eq (Some scp) tcb_scps curthread \<longrightarrow> scp = cursc) \<and>
    (\<forall>tp. pred_map_eq (Some cursc) tcb_scps tp \<longrightarrow> tp = curthread)"

abbreviation cur_sc_tcb_only_sym_bound :: "'z state \<Rightarrow> bool" where
  "cur_sc_tcb_only_sym_bound s \<equiv> cur_sc_tcb_only_sym_bound_2 (cur_sc s) (cur_thread s) (tcb_scps_of s)"

lemmas cur_sc_tcb_only_sym_bound_def = cur_sc_tcb_only_sym_bound_2_def

lemma strengthen_cur_sc_chargeable:
  "cur_sc_tcb_only_sym_bound s \<Longrightarrow> cur_sc_chargeable s"
  unfolding cur_sc_chargeable_def cur_sc_tcb_only_sym_bound_def
  apply (intro conjI; intro allI impI)
   apply (drule conjunct1, clarsimp)
  apply (drule conjunct2, clarsimp)
  done

lemma cur_sc_tcb_are_bound_cur_sc_chargeable:
  "\<lbrakk>cur_sc_tcb_are_bound s; heap_refs_retract (tcb_scps_of s) (sc_tcbs_of s)\<rbrakk>
   \<Longrightarrow> cur_sc_tcb_only_sym_bound s"
  unfolding cur_sc_tcb_only_sym_bound_def
  apply (intro conjI; clarsimp)
   apply (clarsimp simp: vs_all_heap_simps)
  apply (drule (1) heap_refs_retractD[rotated])+
  by (clarsimp simp: vs_all_heap_simps)

lemma cur_sc_tcb_only_sym_bound_cur_sc_not_in_release_q:
  "\<lbrakk>cur_sc_tcb_only_sym_bound s; ct_not_in_release_q s\<rbrakk> \<Longrightarrow> sc_not_in_release_q (cur_sc s) s"
  apply (clarsimp simp: cur_sc_tcb_only_sym_bound_def not_in_release_q_def vs_all_heap_simps)
  apply fastforce
  done

lemma invs_strengthen_cur_sc_chargeable:
  "cur_sc_tcb_are_bound s \<and> invs s \<Longrightarrow> cur_sc_chargeable s"
  by (auto dest!: invs_sym_refs intro!: strengthen_cur_sc_chargeable cur_sc_tcb_are_bound_cur_sc_chargeable)

lemma cur_sc_chargeableD:
  "bound_sc_tcb_at (\<lambda>x. x = Some (cur_sc s)) x s \<Longrightarrow>
   cur_sc_chargeable s \<Longrightarrow> (x = cur_thread s \<or> st_tcb_at inactive x s)"
   by (clarsimp simp: cur_sc_chargeable_def tcb_at_kh_simps pred_map_simps)

lemma cur_sc_tcb_only_sym_bound_lift_pre_conj:
  assumes A: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  assumes B: "\<And>P. \<lbrace>\<lambda>s. P (cur_sc s)\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_sc s)\<rbrace>"
  assumes C: "\<And>P t. \<lbrace>\<lambda>s. \<not> (bound_sc_tcb_at P t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. \<not> (bound_sc_tcb_at P t s)\<rbrace>"
  shows "\<lbrace>cur_sc_tcb_only_sym_bound and R\<rbrace> f \<lbrace>\<lambda>_. cur_sc_tcb_only_sym_bound\<rbrace>"
  unfolding cur_sc_tcb_only_sym_bound_def
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift C hoare_vcg_disj_lift
           simp: tcb_at_kh_simps[symmetric]
      | wps A B)+

lemmas cur_sc_tcb_only_sym_bound_lift = cur_sc_tcb_only_sym_bound_lift_pre_conj[where R=\<top>, simplified]

lemma active_sc_tcb_at_def2:
  "active_sc_tcb_at t s = ((\<exists>scp. bound_sc_tcb_at (\<lambda>p. p = Some scp) t s \<and> is_active_sc scp s))"
  by (clarsimp simp: vs_all_heap_simps tcb_at_kh_simps)

lemma budget_ready_def2:
  "budget_ready t s = ((\<exists>scp. bound_sc_tcb_at (\<lambda>p. p = Some scp) t s \<and> is_refill_ready scp s))"
  by (clarsimp simp: vs_all_heap_simps tcb_at_kh_simps)

lemma budget_sufficient_def2:
  "budget_sufficient t s = ((\<exists>scp. bound_sc_tcb_at (\<lambda>p. p = Some scp) t s \<and> is_refill_sufficient 0 scp s))"
  by (clarsimp simp: vs_all_heap_simps tcb_at_kh_simps)

lemma budget_ready_def3:
  "active_sc_tcb_at t s
   \<Longrightarrow> budget_ready t s \<longleftrightarrow> tcb_ready_time t s \<le> cur_time s + kernelWCET_ticks"
  by (auto simp: vs_all_heap_simps refill_ready_def tcb_ready_times_defs
                    opt_map_def map_project_def map_join_def pred_map_simps
                    tcb_scps_of_tcbs_def tcbs_of_kh_def
                    sc_refill_cfgs_of_scs_def scs_of_kh_def
             split: option.split)

lemma active_sc_tcb_at_fold:
  "(\<exists>scp. bound_sc_tcb_at (\<lambda>x. x = Some scp) t s \<and> sc_at_pred sc_active scp s)
   = active_sc_tcb_at t s"
  apply (intro iffI)
  apply (clarsimp simp: pred_tcb_at_def sc_at_pred_n_def obj_at_def vs_all_heap_simps is_sc_active_def2 split: option.splits)
  apply (fastforce simp: pred_tcb_at_def sc_at_pred_n_def obj_at_def vs_all_heap_simps is_sc_active_def2 split: option.splits)
  done

\<comment> \<open>Locales that generate various traditional obj_at lemmas from valid_sched_pred etc.\<close>

locale released_ipc_queues_pred_pre_conj_locale =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes f :: "('state_ext state, 'return_t) nondet_monad"
  fixes R :: "'state_ext state \<Rightarrow> bool"
  assumes released_ipc_queues_pred:
    "\<And>P. \<lbrace>\<lambda>s. released_ipc_queues_pred P s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. released_ipc_queues_pred P\<rbrace>"
begin

lemma st_tcb_at_cur_time:
  "\<lbrace>\<lambda>s. N (st_tcb_at (P (cur_time s)) t' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (st_tcb_at (P (cur_time s)) t' s)\<rbrace>"
  apply (wp_pre, rule hoare_lift_Pf_pre_conj[where f=cur_time])
  by (wpsimp wp: valid_sched_pred_heap_proj_lowers released_ipc_queues_pred)+

lemma bound_sc_tcb_at_cur_time:
  "\<lbrace>\<lambda>s. N (bound_sc_tcb_at (P (cur_time s)) t' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (bound_sc_tcb_at (P (cur_time s)) t' s)\<rbrace>"
  apply (wp_pre, rule hoare_lift_Pf_pre_conj[where f=cur_time])
  by (wpsimp wp: valid_sched_pred_heap_proj_lowers released_ipc_queues_pred)+

lemma fault_tcb_at_cur_time:
  "\<lbrace>\<lambda>s. N (fault_tcb_at (P (cur_time s)) t' s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (fault_tcb_at (P (cur_time s)) t' s)\<rbrace>"
  apply (wp_pre, rule hoare_lift_Pf_pre_conj[where f=cur_time])
  by (wpsimp wp: valid_sched_pred_heap_proj_lowers released_ipc_queues_pred)+

lemma sc_refill_cfg_sc_at_cur_time:
  "\<lbrace>\<lambda>s. N (sc_refill_cfg_sc_at (P (cur_time s)) scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_refill_cfg_sc_at (P (cur_time s)) scp s)\<rbrace>"
  apply (wp_pre, rule hoare_lift_Pf_pre_conj[where f=cur_time])
  by (wpsimp wp: valid_sched_pred_heap_proj_lowers released_ipc_queues_pred)+

lemma sc_refills_sc_at_cur_time:
  "\<lbrace>\<lambda>s. N (sc_refills_sc_at (P (cur_time s)) scp s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (sc_refills_sc_at (P (cur_time s)) scp s)\<rbrace>"
  apply (wp_pre, rule hoare_lift_Pf_pre_conj[where f=cur_time])
  by (wpsimp wp: valid_sched_pred_heap_proj_lowers released_ipc_queues_pred)+

end

locale released_ipc_queues_pred_locale =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes f :: "('state_ext state, 'return_t) nondet_monad"
  assumes released_ipc_queues_pred[wp]: "\<And>P. f \<lbrace>released_ipc_queues_pred P\<rbrace>"
begin
  interpretation pre_conj: released_ipc_queues_pred_pre_conj_locale state_ext_t f \<top>
    by (unfold_locales; wpsimp wp: released_ipc_queues_pred)
  lemmas st_tcb_at_cur_time           [wp] = pre_conj.st_tcb_at_cur_time           [simplified]
  lemmas bound_sc_tcb_at_cur_time     [wp] = pre_conj.bound_sc_tcb_at_cur_time     [simplified]
  lemmas fault_tcb_at_cur_time        [wp] = pre_conj.fault_tcb_at_cur_time        [simplified]
  lemmas sc_refill_cfg_sc_at_cur_time [wp] = pre_conj.sc_refill_cfg_sc_at_cur_time [simplified]
  lemmas sc_refills_sc_at_cur_time    [wp] = pre_conj.sc_refills_sc_at_cur_time    [simplified]
end

definition ct_in_q_2 where
  "ct_in_q_2 ct rqs tcb_sts \<equiv>
    pred_map runnable tcb_sts ct \<longrightarrow> in_queues_2 rqs ct"

abbreviation ct_in_q where
  "ct_in_q s \<equiv> ct_in_q_2 (cur_thread s) (ready_queues s) (tcb_sts_of s)"

lemmas ct_in_q_def = ct_in_q_2_def

locale valid_sched_pred_pre_conj_locale =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes f :: "('state_ext::state_ext state, 'return_t) nondet_monad"
  fixes R :: "'state_ext state \<Rightarrow> bool"
  assumes valid_sched_pred: "\<And>P. \<lbrace>\<lambda>s. valid_sched_pred P s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_sched_pred P\<rbrace>"
begin

sublocale released_ipc_queues_pred_pre_conj_locale state_ext_t f R
  by unfold_locales (rule valid_sched_pred)

lemma st_tcb_at_cur_thread:
  "\<lbrace>\<lambda>s. N (st_tcb_at (P (cur_time s)) (cur_thread s) s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (st_tcb_at (P (cur_time s)) (cur_thread s) s)\<rbrace>"
  apply (wp_pre, rule hoare_lift_Pf_pre_conj[where f=cur_thread])
  by (wpsimp wp: st_tcb_at_cur_time valid_sched_pred)+

lemma ct_in_state:
  "\<lbrace>\<lambda>s. ct_in_state P s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. ct_in_state P\<rbrace>"
  by (wpsimp simp: ct_in_state_def wp: st_tcb_at_cur_thread)

lemma cur_tcb:
  "\<lbrace>\<lambda>s. cur_tcb s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  unfolding cur_tcb_def tcb_at_st_tcb_at by (wpsimp wp: st_tcb_at_cur_thread)

lemma bound_sc_tcb_at_cur_thread:
  "\<lbrace>\<lambda>s. N (bound_sc_tcb_at (P (cur_time s)) (cur_thread s) s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (bound_sc_tcb_at (P (cur_time s)) (cur_thread s) s)\<rbrace>"
  apply (wp_pre, rule hoare_lift_Pf_pre_conj[where f=cur_thread])
  by (wpsimp wp: bound_sc_tcb_at_cur_time valid_sched_pred)+

lemma fault_tcb_at_cur_thread:
  "\<lbrace>\<lambda>s. N (fault_tcb_at (P (cur_time s)) (cur_thread s) s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. N (fault_tcb_at (P (cur_time s)) (cur_thread s) s)\<rbrace>"
  apply (wp_pre, rule hoare_lift_Pf_pre_conj[where f=cur_thread])
  by (wpsimp wp: fault_tcb_at_cur_time valid_sched_pred)+

end

abbreviation cur_sc_active where
  "cur_sc_active s \<equiv> is_active_sc (cur_sc s) s"

lemmas cur_sc_active_lift = hoare_lift_Pf[where f=cur_sc and P=is_active_sc and m=f for f, rotated]

abbreviation sc_bounded_release_time :: "sched_context \<Rightarrow> bool" where
  "sc_bounded_release_time sc \<equiv> cfg_bounded_release_time (sc_refill_cfg_of sc)"

locale valid_sched_pred_locale =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes f :: "('state_ext::state_ext state, 'return_t) nondet_monad"
  assumes valid_sched_pred[wp]: "\<And>P. f \<lbrace>valid_sched_pred P\<rbrace>"
begin
  interpretation pre_conj: valid_sched_pred_pre_conj_locale state_ext_t f \<top>
    by (unfold_locales; wpsimp wp: valid_sched_pred)
  sublocale released_ipc_queues_pred_locale state_ext_t f
    by unfold_locales (rule valid_sched_pred)
  lemmas st_tcb_at_cur_thread       [wp] = pre_conj.st_tcb_at_cur_thread       [simplified]
  lemmas ct_in_state                [wp] = pre_conj.ct_in_state                [simplified]
  lemmas cur_tcb                    [wp] = pre_conj.cur_tcb                    [simplified]
  lemmas bound_sc_tcb_at_cur_thread [wp] = pre_conj.bound_sc_tcb_at_cur_thread [simplified]
  lemmas fault_tcb_at_cur_thread    [wp] = pre_conj.fault_tcb_at_cur_thread    [simplified]
end

end
