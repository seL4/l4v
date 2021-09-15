(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Noninterference_Base
imports "Lib.Simulation"
begin

text \<open>
  Toby's extended noninterference definitions to handle dynamic assignment,
  that depends on the current state, of
  the domain that each action is assigned to. This is the gory details
  reported in the the CPP 2012 paper
  \emph{Noninterference for Operating System Kernels}.
\<close>

section \<open>Generic systems\<close>

lemma un_eq:
  "\<lbrakk> S = S'; T = T' \<rbrakk> \<Longrightarrow> S \<union> T = S' \<union> T'"
  by auto

lemma Un_eq:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<in> xs; y \<in> ys \<rbrakk> \<Longrightarrow> P x = Q y; \<exists>x. x \<in> xs; \<exists>y. y \<in> ys \<rbrakk>
     \<Longrightarrow> (\<Union>x \<in> xs. P x) = (\<Union>y \<in> ys. Q y)"
  by auto

lemma Int_eq:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<in> xs; y \<in> ys \<rbrakk> \<Longrightarrow> P x = Q y; \<exists>x. x \<in> xs; \<exists>y. y \<in> ys \<rbrakk>
     \<Longrightarrow> (\<Inter>x \<in> xs. P x) = (\<Inter>y \<in> ys. Q y)"
  by auto

lemma Un_eq_Int:
  assumes ex: "\<exists>x. x \<in> xs"
  assumes ey: "\<exists>y. y \<in> ys"
  assumes a: "\<And>x y. \<lbrakk> x \<in> xs; y \<in> ys \<rbrakk> \<Longrightarrow> S x = S' y"
  shows "(\<Union>x \<in> xs. S x) = (\<Inter>x \<in> ys. S' x)"
  apply (rule equalityI)
   apply (clarsimp)
   apply (drule a, assumption, simp)
  apply clarsimp
  apply (insert ex ey)
  apply clarsimp
  apply (frule a, assumption)
  apply fastforce
  done


subsection\<open>Run function\<close>

primrec Run :: "('e \<Rightarrow> ('s \<times> 's) set) \<Rightarrow> 'e list \<Rightarrow> ('s \<times> 's) set" where
  "Run Stepf []     = Id"
| "Run Stepf (a#as) = Stepf a O Run Stepf as"


lemma Run_mid[rule_format]:
  "(s,u) \<in> Run Stepf (as @ bs) \<longrightarrow> (\<exists>t. (s,t) \<in> Run Stepf as \<and> (t,u) \<in> Run Stepf bs)"
proof (induct as arbitrary: s u bs)
  case Nil show ?case
    by (clarsimp)
next
  case (Cons a as) show ?case
    apply (clarsimp simp: relcomp_def)
    apply (drule "Cons.hyps"[rule_format])
    apply fastforce
    done
qed

lemma Run_trans:
  "\<lbrakk> (s,t) \<in> Run Stepf as; (t,u) \<in> Run Stepf bs \<rbrakk>
     \<Longrightarrow> (s,u) \<in> Run Stepf (as @ bs)"
  by (induct as arbitrary: bs s t u) auto

lemma Run_app:
  "Run Stepf (as @ bs) = (Run Stepf as) O (Run Stepf bs)"
  apply (rule equalityI)
   apply (fastforce dest: Run_mid)
  apply (fastforce intro: Run_trans)
  done


subsection \<open>Base system locale\<close>

text \<open>An ADT with an initial state.\<close>
locale system =
  fixes A :: "('a,'s,'e) data_type"
  and s0 :: "'s"  (* an initial state *)
begin

(* State 's' is reachable from the initial state 's0'. *)
definition reachable where
  "reachable s \<equiv> \<exists>js. s \<in> execution A s0 js"

definition Step where
  "Step a \<equiv> {(s,s') . s' \<in> execution A s [a]}"

(* The system is "observationally deterministic": that is, the
 * observable part of the system is always deterministic. *)
definition obs_det where
  "obs_det \<equiv> \<forall>s js. (\<exists>s'. execution A s js = {s'})"

lemmas obs_detD = obs_det_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

(* The abstraction/concretisation functions "Init"/"Fin"
 * don't abstract away information. *)
definition no_abs where
  "no_abs \<equiv> \<forall>x s as . reachable s
                       \<longrightarrow> x \<in> steps (Simulation.Step A) (Init A s) as
                       \<longrightarrow> Init A (Fin A x) = {x}"

lemmas no_absD = no_abs_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

end


subsection \<open>Enabled system\<close>

text\<open>
  A system that is always enabled.

  In particular, the system will never be in deadlock, and there
  is always an enabled transition from every reachable state.\<close>

locale enabled_system = system +
  assumes enabled: "(\<exists>js. s \<in> execution A s0 js) \<Longrightarrow> \<exists>s'. s' \<in> execution A s js"
begin

lemma reachable_enabled:
  "reachable s \<Longrightarrow> \<exists>s'. s' \<in> execution A s js"
  apply (simp add: reachable_def)
  apply (erule enabled)
  done

lemma enabled_Step:
  "reachable s \<Longrightarrow> \<exists>s'. (s,s') \<in> Step a"
  by (simp add: Step_def, blast intro: reachable_enabled)

end


subsection \<open>Step system\<close>

text \<open>A Step system is a system for which a running
   a sequence of events is equivalent to performing a sequence of individual
   steps: one for each event in the sequence in turn. In other words
   running [a,b,c,...] is the same than running [a] then running [b] then ...
   This correspond to projecting to the observable state and deducing the real
   state from that observable state on each event.

   We define the unwinding conditions on this kind of system\<close>
locale Step_system = system A s0
  for A :: "('a,'s,'e) data_type" and s0 :: "'s"  +
  assumes reachable_s0: "reachable s0"
  assumes execution_Run: "reachable s \<Longrightarrow> execution A s as = {s'. (s,s') \<in> Run Step as}"
begin

lemma execution_Run':
  "s \<in> execution A s0 js \<Longrightarrow> execution A s as = {s'. (s,s') \<in> Run Step as}"
  apply (rule execution_Run)
  apply (fastforce simp: reachable_def)
  done

lemma reachable_Run:
  "reachable s \<Longrightarrow> \<exists>as. (s0,s) \<in> Run Step as"
  apply (clarsimp simp add: reachable_def)
  apply (cut_tac as=js in execution_Run[OF reachable_s0])
  apply blast
  done

lemma Run_reachable:
  "\<exists>as. (s0,s) \<in> Run Step as \<Longrightarrow> reachable s"
  apply (clarsimp simp add: reachable_def)
  apply (cut_tac as=as in execution_Run[OF reachable_s0])
  apply blast
  done

lemma reachable_execution:
  "\<lbrakk> reachable s; s' \<in> execution A s js \<rbrakk> \<Longrightarrow> reachable s'"
  apply (clarsimp simp: reachable_def)
  apply (rule_tac x="jsa @ js" in exI)
  apply (frule execution_Run'[where s=s and as=js])
  apply (simp add: execution_Run[where s=s0, simplified reachable_s0])
  apply (fastforce simp: Run_app)
  done

lemma reachable_Step:
  "\<lbrakk> reachable s; (s,s') \<in> Step a \<rbrakk> \<Longrightarrow> reachable s'"
  apply (erule reachable_execution)
  apply (simp add: Step_def)
  done

lemma reachable_induct_helper:
  assumes a: "\<And>s s' a. \<lbrakk> reachable s; P s; (s, s') \<in> Step a \<rbrakk> \<Longrightarrow> P s'"
  shows "\<lbrakk> (s0, s1) \<in> Run Step as; P s0 \<rbrakk> \<Longrightarrow> P s1"
  apply (induct as arbitrary: s1 rule: rev_induct)
   apply simp
  apply (fastforce dest: Run_mid intro: a Run_reachable)
  done

lemma reachable_induct:
  "\<lbrakk> \<And>s s' a. reachable s \<Longrightarrow> (s,s') \<in> (Step a) \<Longrightarrow> P s \<Longrightarrow> P s'; reachable s1; P s0 \<rbrakk>
     \<Longrightarrow> P s1"
  apply (drule reachable_Run)
  apply (elim exE)
  apply (rule reachable_induct_helper)
    apply simp+
  done

end


subsection \<open>Init Fin system\<close>

text \<open>An Init Fin system a stronger kind of Step system where know directly
   that Fin and Init behave nicely as nearly "inverse" of each other which imply
   that projecting to observable state then deducing the original state behave
   as expected in Step system.
\<close>

locale Init_Fin_system = system A s0
  for A :: "('a,'s,'e) data_type" and s0 :: "'s"  +
  assumes reachable_s0: "reachable s0"
  assumes Fin_Init: "reachable s \<Longrightarrow> Fin A ` Init A s = {s}"
  assumes Init_Fin: "\<lbrakk> reachable s; x \<in> steps (Simulation.Step A) (Init A s) as \<rbrakk>
                       \<Longrightarrow> x \<in> Init A (Fin A x)"
  assumes obs_det_or_no_abs: "obs_det \<or> no_abs"
begin

lemma execution_subset_Run:
  "reachable s \<Longrightarrow> execution A s as \<subseteq> {s'. (s,s') \<in> Run Step as}"
  apply (induct as arbitrary: s rule: rev_induct)
   apply (simp add: execution_def steps_def Fin_Init)
  apply (simp add: execution_def steps_def)
  apply (rule subsetI)
  apply clarsimp
  apply (rule Run_trans)
   apply blast
  apply (cut_tac x=xc and s=s and as=xs in Init_Fin, (simp add: steps_def)+)
  apply (clarsimp simp: Step_def execution_def steps_def)
  apply blast
  done

lemma Run_subset_execution:
  "\<lbrakk> no_abs; reachable s \<rbrakk> \<Longrightarrow> {s'. (s,s') \<in> Run Step as} \<subseteq> execution A s as"
  apply (induct as arbitrary: s rule: rev_induct)
   apply (simp add: execution_def steps_def Fin_Init)
  apply (simp add: execution_def steps_def)
  apply (rule subsetI)
  apply clarsimp
  apply (drule Run_mid)
  apply clarsimp
  apply (drule_tac x=s in meta_spec)
  apply clarsimp
  apply (drule_tac subsetD)
   apply blast
  apply (clarsimp simp: Image_def image_def Step_def execution_def steps_def)
  apply (rule_tac x=xc in exI)
  apply clarsimp
  apply (rule_tac x=xd in bexI)
   apply assumption
  apply (drule_tac x=xb in no_absD)
    apply (simp add: steps_def Image_def)+
  done

lemma Run_det:
  "obs_det \<Longrightarrow> \<exists>s'. {s'. (s,s') \<in> Run Step as} = {s'}"
  apply (induct as arbitrary: s rule: rev_induct)
   apply simp
  apply (simp add: Run_app relcomp_def)
  apply (drule_tac x=s in meta_spec)
  apply clarsimp
  apply (drule_tac s=s' and js="[x]" in obs_detD)
  apply (clarsimp simp: Step_def)
  apply (rule_tac x="s'a" in exI)
  apply (auto dest: equalityD1)
  done

lemma eq:
  "\<lbrakk> S \<subseteq> T; \<exists>x. S = {x}; \<exists>y. T = {y} \<rbrakk> \<Longrightarrow> S = T"
  by blast

lemma execution_Run:
  "reachable s \<Longrightarrow> execution A s as = {s'. (s,s') \<in> Run Step as}"
  apply (rule disjE[OF obs_det_or_no_abs])
   apply (rule eq)
     apply (erule execution_subset_Run)
    apply (erule obs_detD)
   apply (erule Run_det)
  apply (rule equalityI)
   apply (erule execution_subset_Run)
  apply (erule (1) Run_subset_execution)
  done

end


lemma Init_Fin_system_Step_system:
  "Init_Fin_system A s0 \<Longrightarrow> Step_system A s0"
  apply (unfold_locales)
   apply (erule Init_Fin_system.reachable_s0)
  apply (erule (1) Init_Fin_system.execution_Run)
  done

sublocale Init_Fin_system \<subseteq> Step_system
  apply (rule Init_Fin_system_Step_system)
  apply (unfold_locales)
  done


subsection \<open>Init inv Fin system\<close>

text \<open>Here we go one step further than the Init_Fin_system:
  In this local Init and Fin are actually inverse of each other
  Fin is injective
  if s : range Fin A then Init A s = {s'} and Fin A s' = s else Init A s = {}.

  The internal state space is thus just a restriction of the observable state space.
\<close>

(* when Init is the inverse image of Fin, the above assumptions are met by a system
   for which Fin is injective, or one that appears deterministic to an observer *)
locale Init_inv_Fin_system = system A s0
  for A :: "('a,'s,'e) data_type" and s0 :: "'s" +
  assumes Fin_Init_s0: "s0 \<in> Fin A ` Init A s0"
  assumes Init_inv_Fin: "reachable s \<Longrightarrow> Init A s = {s'. Fin A s' = s}"
  assumes Fin_inj: "inj (Fin A)"
begin

lemma inv_and_inj: "reachable s \<Longrightarrow> Fin A i = s \<Longrightarrow> Init A s = {i}"
  using Fin_inj Init_inv_Fin by (blast dest: injD)

lemma s0_reachable:
  "reachable s0"
  apply (simp add: reachable_def)
  apply (rule_tac x="[]" in exI)
  apply (simp add: execution_def steps_def)
  using Fin_Init_s0 .

lemma foldl_foldl_Step:
  "\<lbrakk> x \<in> foldl (\<lambda>S j. data_type.Step A j `` S) M as;
     M \<subseteq> foldl (\<lambda>S j. data_type.Step A j `` S) B js \<rbrakk>
     \<Longrightarrow> x \<in> foldl (\<lambda>S j. data_type.Step A j `` S) (foldl (\<lambda>S j. data_type.Step A j `` S) B js) as"
  apply (induct as arbitrary: x M js B rule: rev_induct)
   apply fastforce
  apply simp
  apply (erule ImageE)
  apply (drule_tac x=xb in meta_spec)
  apply (drule_tac x=M in meta_spec)
  apply simp
  apply (drule_tac x=js in meta_spec)
  apply (drule_tac x=B in meta_spec, simp)
  apply (blast)
  done

lemma reachable_Fin:
  "\<lbrakk> reachable s; x \<in> steps (Simulation.Step A) (Init A s) as \<rbrakk>
     \<Longrightarrow> reachable (Fin A x)"
  apply (cut_tac s=s in Init_inv_Fin, assumption)
  apply (clarsimp simp: reachable_def execution_def steps_def)
  apply (rule_tac x="js@as" in exI)
  apply (rule imageI)
  apply (subgoal_tac "{s'. Fin A s' = Fin A xa} = {xa}")
   apply simp
   apply (erule foldl_foldl_Step)
   apply blast
  apply (blast dest: injD[OF Fin_inj])
  done

end


lemma Init_inv_Fin_system_Init_Fin_system:
  "Init_inv_Fin_system A s0 \<Longrightarrow> Init_Fin_system A s0"
  apply (unfold_locales)
     apply (erule Init_inv_Fin_system.s0_reachable)
    apply (simp add: Init_inv_Fin_system.Init_inv_Fin)
    apply (simp add: image_def)
    apply (fastforce simp: system.reachable_def execution_def)
   apply (cut_tac s="Fin A x" in Init_inv_Fin_system.Init_inv_Fin)
     apply assumption
    apply (blast intro: Init_inv_Fin_system.reachable_Fin)
   apply simp
  apply (rule disjI2)
  apply (clarsimp simp: system.no_abs_def)
  apply (frule Init_inv_Fin_system.Fin_inj)
  apply (cut_tac s="Fin A x" in Init_inv_Fin_system.Init_inv_Fin)
    apply assumption
   apply (blast intro: Init_inv_Fin_system.reachable_Fin)
  apply simp
  apply (fastforce dest: injD)
  done

sublocale Init_inv_Fin_system \<subseteq> Init_Fin_system
  apply (rule Init_inv_Fin_system_Init_Fin_system)
  apply (unfold_locales)
  done


section \<open>Non interference\<close>

subsection \<open>Policy\<close>

text\<open>This local represent an whole infoflow policy with the all the field needed
       for defining non leakage, non interference and non influence\<close>

locale noninterference_policy =
  fixes dom :: "'e \<Rightarrow> 's \<Rightarrow> 'd"        (* dynamic dom assignment *)
  fixes uwr :: "'d \<Rightarrow> ('s \<times> 's) set"  (* unwinding relation *)
  fixes policy :: "('d \<times> 'd) set"     (* who can send info to whom *)
  fixes out :: "'d \<Rightarrow> 's \<Rightarrow> 'p"        (* observable parts of d in state s *)
  fixes schedDomain :: "'d"
  assumes uwr_equiv_rel: "equiv UNIV (uwr u)"
  assumes schedIncludesCurrentDom:
    "(s,t) \<in> uwr schedDomain \<Longrightarrow> dom e s = dom e t"
  assumes schedFlowsToAll:
    "(schedDomain,d) \<in> policy"
  assumes schedNotGlobalChannel:
    "(x,schedDomain) \<in> policy \<Longrightarrow> x = schedDomain"
begin

abbreviation uwr2 :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool" ("(_/ \<sim>_\<sim>/ _)" [50,100,50] 1000) where
  "s \<sim>u\<sim> t \<equiv> (s,t) \<in> uwr u"

abbreviation policy2 :: "'d \<Rightarrow> 'd \<Rightarrow> bool" (infix "\<leadsto>" 50) where
  "u \<leadsto> v \<equiv> (u,v) \<in> policy"

lemma uwr_refl:
  "s \<sim>(u::'d)\<sim> s"
  apply (cut_tac u=u in uwr_equiv_rel)
  apply (clarsimp simp: equiv_def)
  apply (blast dest: refl_onD)
  done

lemma uwr_sym:
  "x \<sim>(u::'d)\<sim> y \<Longrightarrow> y \<sim>u\<sim> x"
  apply (cut_tac u=u in uwr_equiv_rel)
  apply (clarsimp simp: equiv_def)
  apply (blast dest: symD)
  done

lemma uwr_trans:
  "\<lbrakk> x \<sim>(u::'d)\<sim> y; y \<sim>u\<sim> z \<rbrakk> \<Longrightarrow> x \<sim>u\<sim> z"
  apply (cut_tac u=u in uwr_equiv_rel)
  apply (clarsimp simp: equiv_def)
  apply (blast dest: transD)
  done

definition sameFor_dom :: "'s \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> bool"  ("(_/ \<approx>_\<approx>/ _)" [50,100,50] 1000) where
  "s \<approx>us\<approx> t \<equiv> \<forall>u\<in>us. (s,t) \<in> uwr u"

lemma sameFor_subset_dom: "\<lbrakk>s \<approx>(x::'d set)\<approx> t; y \<subseteq> x\<rbrakk> \<Longrightarrow> s \<approx>y\<approx> t"
  by (fastforce simp: sameFor_dom_def)

lemma sameFor_inter_domI: "s \<approx>(S::'d set)\<approx> t \<Longrightarrow> s \<approx>(S \<inter> B)\<approx> t"
  by (auto simp: sameFor_dom_def)

lemma sameFor_sym_dom:
  "s \<approx>(S::'d set)\<approx> t \<Longrightarrow> t \<approx>S\<approx> s"
  by (auto simp: sameFor_dom_def uwr_sym)

end


subsection \<open>Non interference system\<close>

locale noninterference_system =
  enabled_system A s0 + noninterference_policy dom uwr policy out schedDomain
  for A :: "('a,'s,'e) data_type"
  and s0 :: "'s"
  and dom :: "'e \<Rightarrow> 's \<Rightarrow> 'd"
  and uwr :: "'d \<Rightarrow> ('s \<times> 's) set"
  and policy :: "('d \<times> 'd) set"
  and out :: "'d \<Rightarrow> 's \<Rightarrow> 'p"
  and schedDomain :: "'d"
begin

(* The set of domains (which carry out actions in the list "as") which
 * may influence "u", assuming we start in state "s". *)
primrec sources :: "'e list \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd set" where
  sources_Nil: "sources [] s u = {u}"
| sources_Cons: "sources (a#as) s u =
    (\<Union>{sources as s' u| s'. (s,s') \<in> Step a}) \<union>
    {w. w = dom a s \<and> (\<exists>v s'. dom a s \<leadsto> v \<and> (s,s') \<in> Step a \<and> v \<in> sources as s' u)}"

declare sources_Nil [simp del]
declare sources_Cons [simp del]

definition obs_equiv :: "'s \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> 'd \<Rightarrow> bool" where
  "obs_equiv s as t bs d \<equiv>
     \<forall>s' t'. s' \<in> execution A s as \<and> t' \<in> execution A t bs \<longrightarrow> out d s' = out d t'"

definition uwr_equiv :: "'s \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> 'd \<Rightarrow> bool" where
  "uwr_equiv s as t bs d \<equiv>
     \<forall>s' t'. s' \<in> execution A s as \<and> t' \<in> execution A t bs \<longrightarrow> s' \<sim>d\<sim> t'"


text \<open>Nonleakage\<close>
definition Nonleakage :: "bool" where
  "Nonleakage \<equiv> \<forall>as s u t. reachable s \<and> reachable t
                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                            \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                            \<longrightarrow> obs_equiv s as t as u"


text \<open>A generalisation of Nonleakage.\<close>
definition Nonleakage_gen :: "bool" where
  "Nonleakage_gen \<equiv>
     \<forall>as s u t. reachable s \<and> reachable t
                \<longrightarrow> s \<sim>schedDomain\<sim> t
                \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                \<longrightarrow> uwr_equiv s as t as u"


lemma uwr_equiv_sym:
  "uwr_equiv s as t bs u \<Longrightarrow> uwr_equiv t bs s as u"
  by (fastforce simp: uwr_equiv_def uwr_sym)

lemma uwr_equiv_trans:
  "\<lbrakk> reachable t; uwr_equiv s as t bs x; uwr_equiv t bs u cs x \<rbrakk>
     \<Longrightarrow> uwr_equiv s as u cs x"
  apply (clarsimp simp: uwr_equiv_def)
  apply (cut_tac s=t and js=bs in reachable_enabled)
   apply assumption
  apply (blast intro: uwr_trans)
  done

primrec gen_purge :: "('e list \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd set) \<Rightarrow> 'd \<Rightarrow> 'e list \<Rightarrow> 's set \<Rightarrow> 'e list" where
  Nil: "gen_purge source_func u [] ss = []"
| Cons: "gen_purge source_func u (a#as) ss =
           (if \<exists>s\<in>ss. dom a s \<in> source_func (a#as) s u
            then a # gen_purge source_func u as (\<Union>s\<in>ss. {s'. (s,s') \<in> Step a})
            else gen_purge source_func u as ss)"

definition ipurge where
  "ipurge \<equiv> gen_purge sources"

lemma ipurge_Nil:
  "ipurge u [] ss = []"
  by (auto simp: ipurge_def)

lemma ipurge_Cons:
  "ipurge u (a#as) ss = (if (\<exists>s\<in>ss. dom a s \<in> sources (a#as) s u)
                         then a#ipurge u as (\<Union>s\<in>ss. {s'. (s,s') \<in> Step a})
                         else ipurge u as ss)"
  by (auto simp: ipurge_def)

lemma gen_purge_shortens:
  "length (gen_purge sf u as ss) \<le> length as"
  apply (induct as arbitrary: ss; clarsimp)
  apply (rule le_trans)
   apply assumption
  apply simp
  done

lemma INT_cong':
  assumes a: "\<And>x. Q x \<Longrightarrow> P x = P' x"
  shows "\<Inter>{P x|x. Q x} = \<Inter>{P' x|x. Q x}"
  by (auto simp: a)


text \<open>Standard Noninterference\<close>
definition Noninterference :: bool where
 "Noninterference \<equiv> \<forall>u as s. reachable s \<longrightarrow> (obs_equiv s as s (ipurge u as {s}) u)"


text \<open>Strong Noninterference\<close>
definition Noninterference_strong :: bool where
  "Noninterference_strong \<equiv> \<forall>u as bs s. reachable s
                                         \<longrightarrow> ipurge u as {s} = ipurge u bs {s}
                                         \<longrightarrow> obs_equiv s as s bs u"


lemma obs_equiv_sym:
  "obs_equiv s as t bs u \<Longrightarrow> obs_equiv t bs s as u"
  by (clarsimp simp: obs_equiv_def)

lemma obs_equiv_trans:
  "\<lbrakk> reachable t; obs_equiv s as t bs u; obs_equiv t bs x cs u \<rbrakk>
     \<Longrightarrow> obs_equiv s as x cs u"
  apply (clarsimp simp: obs_equiv_def)
  apply (cut_tac s=t and js=bs in reachable_enabled, assumption, blast)
  done

lemma Noninterference_Noninterference_strong:
  "Noninterference \<Longrightarrow> Noninterference_strong"
  apply (clarsimp simp: Noninterference_def Noninterference_strong_def)
  apply (drule_tac x=u in spec)
  apply (frule_tac x=as in spec, drule_tac x=s in spec)
  apply (drule_tac x=bs in spec, drule_tac x=s in spec)
  apply clarsimp
  apply (rule obs_equiv_trans)
    apply assumption
   apply assumption
  apply (erule obs_equiv_sym)
  done


text \<open>
  Noninfluence -- the combination of Noninterference and Nonleakage.
  We add the assumption about equivalence wrt the scheduler's domain, as
  is common in e.g. GVW.
\<close>
definition Noninfluence :: bool where
 "Noninfluence \<equiv>
    \<forall>u as s t. reachable s \<and> reachable t
               \<longrightarrow> s \<approx>(sources as s u)\<approx> t
               \<longrightarrow> s \<sim>schedDomain\<sim> t
               \<longrightarrow> obs_equiv s as t (ipurge u as {t}) u"

definition Noninfluence_strong  :: "bool"
where
 "Noninfluence_strong \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                      \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                                      \<longrightarrow> s \<sim>schedDomain\<sim> t
                                      \<longrightarrow> ipurge u as {s} = ipurge u bs {s}
                                      \<longrightarrow> obs_equiv s as t bs u"


lemma notin_policyI:
  "\<lbrakk> dom a s \<notin> sources (a # list) s u; \<exists>s'. (s,s') \<in> Step a \<and> ua \<in> sources list s' u \<rbrakk>
     \<Longrightarrow> (dom a s,ua) \<notin> policy"
  by (clarsimp simp: sources_Cons)

lemma Noninfluence_strong_Noninterference_strong:
  "Noninfluence_strong \<Longrightarrow> Noninterference_strong"
  apply (clarsimp simp: Noninfluence_strong_def Noninterference_strong_def)
  apply (drule_tac x=u in spec, drule_tac x=as in spec, drule_tac x=bs in spec)
  apply (fastforce simp: sameFor_dom_def uwr_refl)
  done

lemma Noninfluence_strong_Nonleakage:
  "Noninfluence_strong \<Longrightarrow> Nonleakage"
  by (clarsimp simp: Noninfluence_strong_def Nonleakage_def)


text \<open>This stronger condition is needed
   to make the induction proof work for Noninterference. It can be viewed
   as a generalisation of Noninfluence; hence its name here.
\<close>
definition Noninfluence_gen :: bool where
  "Noninfluence_gen \<equiv> \<forall>u as s ts. reachable s \<and> (\<forall>t \<in> ts. reachable t)
                                   \<longrightarrow> (\<forall>t \<in> ts. s \<approx>(sources as s u)\<approx> t)
                                   \<longrightarrow> (\<forall>t \<in> ts. s \<sim>schedDomain\<sim> t)
                                   \<longrightarrow> (\<forall>t \<in> ts. uwr_equiv s as t (ipurge u as ts) u)"

definition Noninfluence_uwr  :: bool where
  "Noninfluence_uwr \<equiv> \<forall>u as s t. reachable s \<and> reachable t
                                  \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                                  \<longrightarrow> s \<sim>schedDomain\<sim> t
                                  \<longrightarrow> uwr_equiv s as t (ipurge u as {t}) u"

definition Noninfluence_strong_uwr :: bool where
  "Noninfluence_strong_uwr \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                            \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                                            \<longrightarrow> ipurge u as {s} = ipurge u bs {s}
                                            \<longrightarrow> uwr_equiv s as t bs u"

definition output_consistent :: bool where
  "output_consistent \<equiv> \<forall>u s s'. s \<sim>u\<sim> s'  \<longrightarrow> (out u s = out u s')"

definition confidentiality_u :: bool where
  "confidentiality_u \<equiv> \<forall>a u s t. reachable s \<and> reachable t
                                  \<longrightarrow> s \<sim>schedDomain\<sim> t
                                  \<longrightarrow> ((dom a s \<leadsto> u) \<longrightarrow> s \<sim>dom a s\<sim> t)
                                  \<longrightarrow> s \<sim>u\<sim> t
                                  \<longrightarrow> (\<forall>s' t'. (s,s') \<in> Step a \<and> (t,t') \<in> Step a \<longrightarrow> s' \<sim>u\<sim> t')"

lemma no_domain_visible_nondeterminism:
  "\<lbrakk> confidentiality_u; reachable s; (s,s') \<in> Step a; (s,s'') \<in> Step a \<rbrakk>
     \<Longrightarrow> s' \<sim>d\<sim> s''"
  apply (clarsimp simp: confidentiality_u_def)
  apply (fastforce intro: uwr_refl)
  done

definition integrity_u :: bool where
  "integrity_u \<equiv>
     \<forall>a u s. reachable s \<longrightarrow> (dom a s,u) \<notin> policy \<longrightarrow> (\<forall>s'. (s,s') \<in> Step a \<longrightarrow> s \<sim>u\<sim> s')"

(*<*)
(* integrity_u actually guarantees this (seemingly) stronger condition *)
definition integrity_u_more :: bool where
  "integrity_u_more \<equiv> \<forall>a u s. reachable s
                               \<longrightarrow> (dom a s,u) \<notin> policy
                               \<longrightarrow> (\<forall>s' t. s \<sim>u\<sim> t \<and> (s,s') \<in> Step a \<longrightarrow> s' \<sim>u\<sim> t)"

lemma integrity_u_more:
  "integrity_u \<Longrightarrow> integrity_u_more"
  apply (clarsimp simp: integrity_u_more_def integrity_u_def)
  apply (blast dest: uwr_sym uwr_trans)
  done
(*>*)

lemma integrity_uD:
  "\<lbrakk> integrity_u; reachable s; (dom a s,u) \<notin> policy; s \<sim>u\<sim> t; (s,s') \<in> Step a \<rbrakk>
     \<Longrightarrow> s' \<sim>u\<sim> t"
  apply (drule integrity_u_more)
  apply (simp add: integrity_u_more_def)
  done

text \<open>
  A weaker version of @{prop confidentiality_u} that, with
  @{prop integrity_u}, implies it.
\<close>
definition confidentiality_u_weak where
  "confidentiality_u_weak \<equiv> \<forall>a u s t. reachable s \<and> reachable t
                                       \<longrightarrow> s \<sim>schedDomain\<sim> t
                                       \<longrightarrow> dom a s \<leadsto> u
                                       \<longrightarrow> s \<sim>(dom a s)\<sim> t
                                       \<longrightarrow> s \<sim>u\<sim> t
                                       \<longrightarrow> (\<forall>s' t'. (s,s') \<in> Step a \<and> (t,t') \<in> Step a
                                                    \<longrightarrow> s' \<sim>u\<sim> t')"

lemma confidentiality_u_confidentiality_u_weak:
  "confidentiality_u \<Longrightarrow> confidentiality_u_weak"
  apply (simp add: confidentiality_u_def confidentiality_u_weak_def)
  apply blast
  done

lemma impCE':
  "\<lbrakk> P \<longrightarrow> Q; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R; \<not> P \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by auto

lemma confidentiality_u_weak:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> confidentiality_u"
  apply (clarsimp simp: confidentiality_u_def)
  apply (erule impCE')
   apply (subst (asm) confidentiality_u_weak_def, blast)
  apply (frule integrity_uD, simp+)
  apply (drule_tac s=t and t="s'" in integrity_uD)
      apply assumption
     apply (drule_tac e=a in schedIncludesCurrentDom)
     apply simp
    apply (blast intro: uwr_sym)
   apply assumption
  apply (erule uwr_sym)
  done

lemma obs_equivI:
  "\<lbrakk> output_consistent; uwr_equiv s as t bs ob \<rbrakk> \<Longrightarrow> obs_equiv s as t bs ob"
  apply (clarsimp simp: obs_equiv_def)
  apply (auto simp: uwr_equiv_def output_consistent_def)
  done

lemma Noninfluence_uwr_Noninfluence:
  "\<lbrakk> output_consistent; Noninfluence_uwr \<rbrakk> \<Longrightarrow> Noninfluence"
  apply (clarsimp simp: Noninfluence_def)
  apply (erule obs_equivI)
  apply (auto simp: Noninfluence_uwr_def)
  done

lemma Noninfluence_strong_uwr_Noninfluence_strong:
  "\<lbrakk> output_consistent; Noninfluence_strong_uwr \<rbrakk> \<Longrightarrow> Noninfluence_strong"
  apply (clarsimp simp: Noninfluence_strong_def)
  apply (erule obs_equivI)
  apply (auto simp: Noninfluence_strong_uwr_def)
  done

lemma sched_equiv_preserved:
  "\<lbrakk> confidentiality_u; reachable s; reachable t;
     s \<sim>schedDomain\<sim> t; (s,s') \<in> Step a; (t,t') \<in> Step a \<rbrakk>
     \<Longrightarrow> s' \<sim>schedDomain\<sim> t'"
  apply (case_tac "dom a s = schedDomain")
   apply (subst (asm) confidentiality_u_def)
   apply (drule_tac x=a in spec)
   apply (drule_tac x=schedDomain in spec)
   apply (drule_tac x=s in spec)
   apply (drule_tac x=t in spec)
   apply simp
  apply (subst (asm) confidentiality_u_def)
  apply (blast intro: schedNotGlobalChannel)
  done

lemma sched_equiv_preserved_left:
  "\<lbrakk> integrity_u; s \<sim>schedDomain\<sim> t;
     dom a s \<noteq> schedDomain; (s,s') \<in> Step a; reachable s \<rbrakk>
     \<Longrightarrow> s' \<sim>schedDomain\<sim> t"
  by (blast intro: integrity_uD schedNotGlobalChannel)

lemma Noninfluence_gen_Noninterference:
  "\<lbrakk> output_consistent; Noninfluence_gen \<rbrakk> \<Longrightarrow> Noninterference"
  apply (clarsimp simp: Noninterference_def Noninfluence_gen_def)
  apply (erule_tac x=u in allE)
  apply (erule_tac x=as in allE)
  apply (erule_tac x=s in allE)
  apply (erule_tac x="{s}" in allE)
  apply (clarsimp simp: sameFor_dom_def uwr_refl)
  apply (blast intro: obs_equivI)
  done

lemma Noninfluence_gen_Noninfluence:
  "\<lbrakk> output_consistent; Noninfluence_gen \<rbrakk> \<Longrightarrow> Noninfluence"
  apply (clarsimp simp: Noninfluence_def Noninfluence_gen_def)
  apply (erule_tac x=u in allE)
  apply (erule_tac x=as in allE)
  apply (erule_tac x=s in allE)
  apply (erule_tac x="{t}" in allE)
  apply (blast intro: obs_equivI)
  done

lemma Noninfluence_gen_Noninfluence_uwr:
  "Noninfluence_gen \<Longrightarrow> Noninfluence_uwr"
  by (clarsimp simp: Noninfluence_uwr_def Noninfluence_gen_def)

lemma Noninfluence_gen_Noninterference_strong:
  "\<lbrakk> output_consistent; Noninfluence_gen \<rbrakk> \<Longrightarrow> Noninterference_strong"
  apply (rule Noninterference_Noninterference_strong)
  apply (blast intro: Noninfluence_gen_Noninterference)
  done

end


subsection \<open>Noninterference on enabled Step system : unwinding system\<close>

locale enabled_Step_system = enabled_system A s0 + Step_system A s0
  for A :: "('a,'s,'e) data_type" and s0 :: "'s"

(* we define the unwinding conditions for any system *)
locale unwinding_system =
  enabled_Step_system A s0 + noninterference_policy dom uwr policy out schedDomain
  for A :: "('a,'s,'e) data_type"
  and s0 :: "'s"
  and dom :: "'e \<Rightarrow> 's \<Rightarrow> 'd"
  and uwr :: "'d \<Rightarrow> ('s \<times> 's) set"
  and policy :: "('d \<times> 'd) set"
  and out :: "'d \<Rightarrow> 's \<Rightarrow> 'p"
  and schedDomain :: "'d"

sublocale unwinding_system \<subseteq> noninterference_system by unfold_locales

context unwinding_system begin

lemma sources_refl:
  "reachable s \<Longrightarrow> u \<in> sources as s u"
  apply (induct as arbitrary: s)
   apply (simp add: sources_Nil)
  apply (simp add: sources_Cons)
  apply (frule_tac a=a in enabled_Step)
  apply (auto simp: reachable_Step)
  done

lemma schedDomain_in_sources_Cons:
  "\<lbrakk> reachable s; dom a s = schedDomain \<rbrakk>
     \<Longrightarrow> dom a s \<in> sources (a#as) s u"
  apply (unfold sources_Cons)
  apply (erule ssubst)
  apply (rule UnI2)
  apply (clarsimp)
  apply (rule_tac x=u in exI)
  apply (safe)
   apply (rule schedFlowsToAll)
  apply (frule_tac a=a in enabled_Step)
  apply (fastforce dest: sources_refl reachable_Step)
  done

lemma sources_eq':
  "confidentiality_u \<and> s \<sim>schedDomain\<sim> t \<and> reachable s \<and> reachable t
   \<longrightarrow> sources as s u = sources as t u"
proof (induct as arbitrary: s t)
  case Nil show ?case
    by (simp add: sources_Nil)
next
  case (Cons a as) show ?case
    apply (clarsimp simp: sources_Cons)
    apply (rule un_eq)
     apply (simp only: Union_eq, simp only: UNION_eq[symmetric])
     apply (rule Un_eq, clarsimp)
       apply (metis "Cons.hyps"[rule_format] sched_equiv_preserved reachable_Step)
      apply (fastforce intro: enabled_Step)
     apply (fastforce intro: enabled_Step)
    apply (clarsimp simp: schedIncludesCurrentDom)
    apply (rule Collect_cong)
    apply (rule conj_cong, rule refl)
    apply (rule iff_exI)
    apply (metis "Cons.hyps"[rule_format] sched_equiv_preserved reachable_Step enabled_Step)
    done
qed

lemma sources_eq:
  "\<lbrakk> confidentiality_u; s \<sim>schedDomain\<sim> t; reachable s; reachable t \<rbrakk>
     \<Longrightarrow> sources as s u = sources as t u"
  by (rule sources_eq'[rule_format], simp)

lemma sameFor_sources_dom:
  "\<lbrakk> s \<approx>(sources (a#as) s u)\<approx> t; dom a s \<leadsto> x; x \<in> sources as s' u; (s,s') \<in> Step a \<rbrakk>
     \<Longrightarrow> s \<sim>(dom a s)\<sim> t"
  apply (simp add: sameFor_dom_def)
  apply (erule bspec)
  apply (subst sources_Cons)
  apply (rule UnI2)
  apply blast
  done

lemma sources_unwinding_step:
  "\<lbrakk> s \<approx>(sources (a#as) s u)\<approx> t; s \<sim>schedDomain\<sim> t; confidentiality_u;
     (s,s') \<in> Step a; (t,t') \<in> Step a; reachable s; reachable t \<rbrakk>
     \<Longrightarrow> s' \<approx>(sources as s' u)\<approx> t'"
  apply (clarsimp simp: sameFor_dom_def sources_Cons)
  apply (subst (asm) confidentiality_u_def)
  apply (drule_tac x=a in spec)
  apply (drule_tac x=ua in spec)
  apply (drule_tac x=s in spec)
  apply (drule_tac x=t in spec)
  apply (fastforce intro: sameFor_sources_dom)
  done

lemma ipurge_eq'_helper:
  "\<lbrakk> s \<in> ss; dom a s \<in> sources (a # as) s u; \<forall>s\<in>ts. dom a s \<notin> sources (a # as) s u;
     (\<forall>s t. s \<in> ss \<and> t \<in> ts \<longrightarrow> s \<sim>schedDomain\<sim> t \<and> reachable s \<and> reachable t);
     t \<in> ts; confidentiality_u \<rbrakk>
     \<Longrightarrow> False"
  apply (cut_tac s=s and t=t and as=as and u=u in sources_eq, simp+)
  apply (clarsimp  simp: sources_Cons | safe)+
   apply (rename_tac s')
   apply (drule_tac x=t in bspec, simp)
   apply clarsimp
   apply (cut_tac s=t in enabled_Step, simp)
   apply (erule exE, rename_tac t')
   apply (drule_tac x="sources as t' u" in spec)
   apply (cut_tac s=s' and t=t' and u=u in sources_eq, simp+)
      apply (fastforce elim: sched_equiv_preserved)
     apply (fastforce intro: reachable_Step)
    apply (fastforce intro: reachable_Step)
   apply (fastforce simp: schedIncludesCurrentDom)
  apply (drule_tac x=t in bspec, simp)
  apply clarsimp
  apply (rename_tac v s')
  apply (drule_tac x=v in spec, erule impE, fastforce simp: schedIncludesCurrentDom)
  apply (cut_tac s=t in enabled_Step[where a=a], simp, clarsimp, rename_tac t')
  apply (cut_tac s=s' and t=t' and u=u in sources_eq, simp+)
     apply (fastforce elim: sched_equiv_preserved)
    apply (fastforce intro: reachable_Step)
   apply (fastforce intro: reachable_Step)
  apply (fastforce simp: schedIncludesCurrentDom)
  done

lemma ipurge_eq':
  "(\<forall>s t. s\<in>ss \<and> t\<in>ts \<longrightarrow> s \<sim>schedDomain\<sim> t \<and> reachable s \<and> reachable t) \<and>
   (\<exists>s. s \<in> ss) \<and> (\<exists>t. t \<in> ts) \<and> confidentiality_u
   \<longrightarrow> ipurge u as ss = ipurge u as ts"
proof (induct as arbitrary: ss ts)
  case Nil show ?case
    apply (simp add: ipurge_def)
    done
next
  case (Cons a as) show ?case
    apply (clarsimp simp: ipurge_Cons schedIncludesCurrentDom)
    apply (intro conjI impI)
       apply (rule "Cons.hyps"[rule_format])
       apply clarsimp
       apply (metis sched_equiv_preserved reachable_Step enabled_Step)
      apply clarsimp
      apply (drule ipurge_eq'_helper, simp+)[1]
     apply clarsimp
     apply (drule ipurge_eq'_helper, (simp add: uwr_sym)+)[1]
    apply (rule "Cons.hyps"[rule_format], auto)
    done
qed

lemma ipurge_eq:
  "\<lbrakk> s \<sim>schedDomain\<sim> t; reachable s; reachable t; confidentiality_u \<rbrakk>
     \<Longrightarrow> ipurge u as {s} = ipurge u as {t}"
  by (rule ipurge_eq'[rule_format], simp)

lemma Noninfluence_uwr_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u; Noninfluence_uwr \<rbrakk> \<Longrightarrow> Noninfluence_strong_uwr"
  apply (clarsimp simp: Noninfluence_uwr_def Noninfluence_strong_uwr_def)
  apply (frule_tac s=s and t=t and as=as and u=u in ipurge_eq)
     apply assumption+
  apply (frule_tac s=s and t=t and as=bs and u=u in ipurge_eq)
     apply assumption+
  apply clarsimp
  apply (drule_tac x=u in spec)
  apply (frule_tac x=as in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (drule_tac x=bs in spec)
  apply (drule_tac x=t in spec, drule_tac x=t in spec)
  apply clarsimp
  apply (rule_tac t=t in uwr_equiv_trans)
    apply assumption
   apply assumption
  apply (rule uwr_equiv_sym)
  apply (clarsimp simp: sameFor_dom_def uwr_refl)
  done

lemma Noninfluence_Noninfluence_strong:
  "\<lbrakk> confidentiality_u; Noninfluence \<rbrakk> \<Longrightarrow> Noninfluence_strong"
  apply (clarsimp simp: Noninfluence_def Noninfluence_strong_def)
  apply (frule_tac s=s and t=t and as=as and u=u in ipurge_eq)
     apply assumption+
  apply (frule_tac s=s and t=t and as=bs and u=u in ipurge_eq)
     apply assumption+
  apply clarsimp
  apply (drule_tac x=u in spec)
  apply (frule_tac x=as in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (drule_tac x=bs in spec)
  apply (drule_tac x=t in spec, drule_tac x=t in spec)
  apply clarsimp
  apply (rule_tac t=t in obs_equiv_trans)
    apply assumption
   apply assumption
  apply (rule obs_equiv_sym)
  apply (clarsimp simp: sameFor_dom_def uwr_refl)
  done

lemma dom_in_sources_Cons:
  "\<lbrakk> confidentiality_u; reachable s; reachable t; s \<approx>(sources (a#as) s u)\<approx> t;
     s \<sim>schedDomain\<sim> t; (dom a s \<in> sources (a#as) s u) \<rbrakk>
     \<Longrightarrow> (dom a t \<in> sources (a#as) t u)"
  apply (subgoal_tac "dom a s = dom a t")
   apply (fastforce dest: sources_eq)
  apply (blast intro: schedIncludesCurrentDom)
  done

lemma uwr_equiv_Cons_bothI:
  "\<lbrakk> reachable s; reachable t;
      \<forall>s' t'. (s,s') \<in> Step a \<and> (t,t') \<in> Step b \<longrightarrow> uwr_equiv s' as t' bs u \<rbrakk>
     \<Longrightarrow> uwr_equiv s (a # as) t (b # bs) u"
  by (fastforce simp: uwr_equiv_def execution_Run reachable_Step)

lemma uwr_equiv_Cons_leftI:
  "\<lbrakk> reachable s; \<forall>s'. (s,s') \<in> Step a \<longrightarrow> uwr_equiv s' as t bs u \<rbrakk>
     \<Longrightarrow> uwr_equiv s (a # as) t bs u"
  by (fastforce simp: uwr_equiv_def execution_Run reachable_Step)

lemma notin_policyI':
  "\<lbrakk> reachable s; dom a s \<notin> sources (a # list) s u; (s,s') \<in> Step a; ua \<in> sources list s' u \<rbrakk>
     \<Longrightarrow> (dom a s,ua) \<notin> policy"
  apply (rule notin_policyI)
   apply auto
  done

lemma sources_eq_Step:
  "\<lbrakk> integrity_u; confidentiality_u; reachable s; (s,s') \<in> Step a; dom a s \<noteq> schedDomain \<rbrakk>
     \<Longrightarrow> (sources as s' u) = (sources as s u)"
  apply (rule sources_eq, simp+)
    apply (rule_tac t=s and s=s and a=a in sched_equiv_preserved_left)
        apply (auto simp add: uwr_refl reachable_Step)
  done

lemma sources_equiv_preserved_left:
  "\<lbrakk> integrity_u; confidentiality_u; reachable s; reachable t; s \<sim>schedDomain\<sim> t;
     dom a s \<notin> sources (a#as) s u; s \<approx>sources (a#as) s u\<approx> t; (s,s') \<in> Step a;
     dom a s \<noteq> schedDomain \<rbrakk>
     \<Longrightarrow> s' \<approx>sources as s' u\<approx> t"
  apply (clarsimp simp: sameFor_dom_def)
  apply (rename_tac v)
  apply (case_tac "(dom a s, v) \<in> policy")
   apply (fastforce simp: sources_Cons)
  apply (fastforce dest: integrity_uD simp: sources_Cons)
  done

lemma Noninfluence_gen:
  "\<lbrakk> confidentiality_u; integrity_u \<rbrakk> \<Longrightarrow> Noninfluence_gen"
  apply (subst Noninfluence_gen_def)
  apply (intro allI)
proof -
  assume conf: "confidentiality_u"
  assume integ: "integrity_u"
  fix u as s ts
  show "reachable s \<and> Ball ts reachable
        \<longrightarrow> Ball ts (sameFor_dom s (sources as s u))
        \<longrightarrow> (\<forall>t\<in>ts. s \<sim>schedDomain\<sim> t)
        \<longrightarrow> (\<forall>t\<in>ts. uwr_equiv s as t (ipurge u as ts) u)"
  proof(induct as arbitrary: s ts)
    case Nil
    show ?case
      apply (clarsimp simp: sameFor_dom_def ipurge_Nil sources_Nil uwr_equiv_def)
      apply (clarsimp simp: execution_Run)
      done
  next
    case (Cons a as)
    show ?case
      apply (clarsimp simp: ipurge_Cons | safe)+
       apply (rule uwr_equiv_Cons_bothI)
         apply assumption
        apply blast
       apply (clarify)
       apply (rename_tac ta tb s' tb')
       apply (rule Cons.hyps[rule_format])
          apply (blast intro: reachable_Step)
         apply (clarsimp)
         apply (rename_tac tc' tc)
      using conf apply (rule_tac s=s and t=tc and a=a in sources_unwinding_step, simp+)[1]
        apply (clarsimp, rename_tac tc' tc)
        apply (rule sched_equiv_preserved[OF conf], (auto simp: sources_refl))[1]
       apply blast
      apply (rename_tac ta)
      apply (rule uwr_equiv_Cons_leftI, blast)
      apply (clarsimp, rename_tac s')
      apply (case_tac "dom a s = schedDomain")
       apply (cut_tac s=s and a=a and as=as and u=u in schedDomain_in_sources_Cons, assumption+)
       apply (metis schedIncludesCurrentDom sources_eq[OF conf])
      apply (rule Cons.hyps[rule_format])
         apply (blast intro: reachable_Step)
        apply (rename_tac tb)
        apply (rule_tac a=a in sources_equiv_preserved_left[OF integ conf], simp+)
           apply (fastforce simp: schedIncludesCurrentDom sources_eq[OF conf])
          apply blast
         apply assumption
        apply assumption
       apply (rule_tac s=s and a=a in sched_equiv_preserved_left[OF integ], simp+)
      done
  qed
qed

lemma Nonleakage_gen:
  "confidentiality_u \<Longrightarrow> Nonleakage_gen"
  apply (subst Nonleakage_gen_def)
  apply (rule allI)
  apply (induct_tac as)
   apply (simp add: sources_Nil uwr_equiv_def execution_Run sameFor_dom_def)
  apply (clarsimp)
  apply (rule uwr_equiv_Cons_bothI)
    apply assumption
   apply assumption
  apply clarsimp
  apply (drule_tac x=s' in spec, drule_tac x=u in spec, drule_tac x=t' in spec)
  apply (clarsimp simp: reachable_Step)
  apply (erule impE)
   apply (blast intro: sched_equiv_preserved)
  apply (erule mp)
  apply (blast intro: sources_unwinding_step)
  done

lemma Noninterference:
  "\<lbrakk> confidentiality_u_weak; output_consistent; integrity_u \<rbrakk>
     \<Longrightarrow> Noninterference"
  apply (rule Noninfluence_gen_Noninterference)
   apply assumption
  apply (blast intro: Noninfluence_gen confidentiality_u_weak)
  done

lemma Noninterference_strong:
  "\<lbrakk> confidentiality_u_weak; output_consistent; integrity_u \<rbrakk>
     \<Longrightarrow> Noninterference_strong"
  apply (rule Noninfluence_gen_Noninterference_strong)
   apply assumption
  apply (blast intro: Noninfluence_gen confidentiality_u_weak)
  done

lemma Noninfluence:
  "\<lbrakk> confidentiality_u_weak; output_consistent; integrity_u \<rbrakk>
     \<Longrightarrow> Noninfluence"
  apply (rule Noninfluence_gen_Noninfluence)
   apply assumption
  apply (blast intro: Noninfluence_gen confidentiality_u_weak)
  done

lemma Noninfluence_strong:
  "\<lbrakk> confidentiality_u_weak; output_consistent; integrity_u \<rbrakk>
     \<Longrightarrow> Noninfluence_strong"
  apply (rule Noninfluence_Noninfluence_strong)
   apply (blast intro: confidentiality_u_weak)
  apply (blast intro: Noninfluence)
  done


lemma Noninfluence_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> Noninfluence_uwr"
  apply (rule Noninfluence_gen_Noninfluence_uwr)
  apply (blast intro: Noninfluence_gen confidentiality_u_weak)
  done

lemma Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> Noninfluence_strong_uwr"
  apply (rule Noninfluence_uwr_Noninfluence_strong_uwr)
   apply (blast intro: confidentiality_u_weak)
  apply (blast intro: Noninfluence_uwr)
  done

lemma sources_Step:
  "\<lbrakk> reachable s; (dom a s, u) \<notin> policy \<rbrakk>
     \<Longrightarrow> sources [a] s u = {u}"
  by (auto simp: sources_Cons sources_Nil enabled_Step dest: enabled_Step)

lemma sources_Step_2:
  "\<lbrakk> reachable s; (dom a s, u) \<in> policy \<rbrakk>
     \<Longrightarrow> sources [a] s u = {dom a s,u}"
  by (auto simp: sources_Cons sources_Nil enabled_Step dest: enabled_Step)

lemma execution_Nil:
  "reachable s \<Longrightarrow> execution A s [] = {s}"
  by (simp add: execution_Run)

lemma Noninfluence_gen_confidentiality_u_weak:
  "Noninfluence_gen \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: Noninfluence_gen_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x="{t}" in spec)
  apply (simp add: sources_Step_2 sameFor_dom_def uwr_equiv_def Step_def
                   ipurge_Cons ipurge_Nil schedIncludesCurrentDom
            split: if_splits)
  done

lemma Noninfluence_strong_uwr_confidentiality_u_weak:
  "Noninfluence_strong_uwr \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: Noninfluence_strong_uwr_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: sources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done

lemma Nonleakage_gen_confidentiality_u:
  "Nonleakage_gen \<Longrightarrow> confidentiality_u"
  apply (clarsimp simp: Nonleakage_gen_def confidentiality_u_def)
  apply (drule_tac x="[a]" in spec, drule_tac x=s in spec)
  apply (drule_tac x=u in spec, drule_tac x=t in spec)
  apply (case_tac "dom a s \<leadsto> u")
   apply (simp add: sources_Step_2 uwr_equiv_def sameFor_dom_def Step_def)
  apply (simp add: sources_Step uwr_equiv_def sameFor_dom_def Step_def)
  done

lemma Nonleakage_gen_equiv_confidentiality_u:
  "Nonleakage_gen = confidentiality_u"
  by (blast intro: Nonleakage_gen_confidentiality_u Nonleakage_gen)

lemma non_sched_doms_cannot_schedule:
  "\<lbrakk> integrity_u; reachable s; dom a s \<noteq> schedDomain; (s,s') \<in> Step a \<rbrakk>
     \<Longrightarrow> s \<sim>schedDomain\<sim> s'"
  apply (drule_tac u=schedDomain in integrity_uD)
      apply assumption
     apply (erule contrapos_nn)
     apply (erule schedNotGlobalChannel)
    apply (rule uwr_refl)
   apply assumption
  apply (erule uwr_sym)
  done


text \<open>
   In systems with just a single event, @{prop integrity_u} is a very strong
   condition. It implies that once the scheduler is not
   running, it can never run again.

   This is one explanation for why seL4 (whose automaton has only a single
   event) doesn't satisfy @{prop integrity_u}.
\<close>
lemma integrity_u_and_single_event_systems:
  "\<lbrakk> integrity_u; reachable s; dom a s \<noteq> schedDomain; s' \<in> execution A s as; \<forall>y. y = a \<rbrakk>
     \<Longrightarrow> dom e s' \<noteq> schedDomain"
  apply (frule_tac x=e in spec)
  apply (erule ssubst)
  apply (rule_tac P="\<lambda>x. x \<noteq> schedDomain" in subst[rotated])
   apply assumption
  apply (induct as arbitrary: s s' a rule: rev_induct)
   apply (simp add: execution_Run)
  apply (simp add: execution_Run)
  apply (drule Run_mid)
  apply (erule exE, rename_tac t)
  apply (drule_tac x=s in meta_spec)
  apply (drule_tac x=t in meta_spec)
  apply (drule_tac x=a in meta_spec)
  apply simp
  apply (rule schedIncludesCurrentDom)
  apply (rule non_sched_doms_cannot_schedule)
     apply assumption
    apply (rule reachable_execution)
     apply assumption
    apply (fastforce simp: execution_Run)
   apply assumption
  apply (drule_tac x=x in spec)
  apply blast
  done

end


subsection \<open>Complete unwinding system\<close>

text \<open>The unwinding conditions are not only sound but also complete when policy is reflexive\<close>
locale complete_unwinding_system = unwinding_system +
  assumes policy_refl: "(u,u) \<in> policy"
begin

lemma Noninfluence_gen_integrity_u:
  "Noninfluence_gen \<Longrightarrow> integrity_u"
  apply (clarsimp simp: Noninfluence_gen_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x="{s}" in spec)
  apply (simp add: sources_Step sameFor_dom_def uwr_equiv_def Step_def ipurge_Cons ipurge_Nil
                   uwr_refl policy_refl execution_Nil uwr_sym
            split: if_splits )
  done

lemma Noninfluence_strong_uwr_integrity_u:
  "Noninfluence_strong_uwr \<Longrightarrow> integrity_u"
  apply (clarsimp simp: Noninfluence_strong_uwr_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: sources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def ipurge_Cons ipurge_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

text \<open>
   @{prop Noninfluence_gen} actually turns out to be equivalent to @{prop Noninfluence_strong_uwr},
   when the policy is reflexive. So the two unwinding conditions for integrity
   and confidentiality actually turn out to be sound and sufficient for the
   condition we were using them to prove in the first place.
\<close>
lemma Noninfluence_gen_equiv_Noninfluence_strong_uwr:
  "Noninfluence_gen = Noninfluence_strong_uwr"
  apply (rule iffI)
   apply (rule Noninfluence_strong_uwr)
    apply (erule Noninfluence_gen_confidentiality_u_weak)
   apply (erule Noninfluence_gen_integrity_u)
  apply (rule Noninfluence_gen)
   apply (rule confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
   apply (erule Noninfluence_strong_uwr_integrity_u)+
  done

end

end
