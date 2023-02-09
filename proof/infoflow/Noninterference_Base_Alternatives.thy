(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Noninterference_Base_Alternatives
  imports
    Noninterference_Base
    Eisbach_Tools.Eisbach_Methods
begin

text \<open>
  This theory explores a bunch of alternative definitions for the @{term sources}
  and @{term ipurge} functions that are the basis of our noninterference formulation
  and shows that they all turn out to yield equivalent noninterference properties.
\<close>
context noninterference_system begin

(* the following definition turns out to yield an information flow property equivalent
   to the above one -- see below *)
primrec xources :: "'e list \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd set" where
  xources_Nil: "xources [] s u = {u}"
| xources_Cons: "xources (a # as) s u =
    (\<Inter>{xources as s' u | s'. (s,s') \<in> Step a}) \<union>
    {w. w = dom a s \<and> (\<forall>s'. (s,s') \<in> Step a \<longrightarrow> (\<exists>v. dom a s \<leadsto> v \<and> v \<in> xources as s' u))}"

lemma in_xources_ConsD:
  "x \<in> (xources (a # as) s u)
   \<Longrightarrow> (\<forall>s'. (s,s') \<in> Step a \<longrightarrow> x \<in> xources as s' u) \<or>
       (x = dom a s \<and> (\<forall>s'. (s,s') \<in> Step a \<longrightarrow> (\<exists>v. dom a s \<leadsto> v \<and> v \<in> xources as s' u)))"
  by auto

lemma in_xources_ConsI1:
  "(\<forall>s'. (s,s') \<in> Step a \<longrightarrow> x \<in> xources as s' u)
   \<Longrightarrow> x \<in> xources (a # as) s u"
  by auto

lemma in_xources_ConsI2:
  "\<lbrakk> x = dom a s; \<forall>s'. (s,s') \<in> Step a \<longrightarrow> (\<exists>v. dom a s \<leadsto> v \<and> v \<in> xources as s' u) \<rbrakk>
     \<Longrightarrow> x \<in> xources (a # as) s u"
  by auto

declare xources_Nil [simp del]
declare xources_Cons [simp del]

lemma xources_subset_xources_Cons:
  "\<Inter>{xources as s' u | s'. (s,s') \<in> Step a} \<subseteq> xources (a # as) s u"
  by (fastforce simp: xources_Cons)

primrec gen_purgx :: "('e list \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'd set) \<Rightarrow> 'd \<Rightarrow> 'e list \<Rightarrow> 's set \<Rightarrow> 'e list" where
  Nil: "gen_purgx sf u [] ss = []"
| Cons: "gen_purgx sf u (a#as) ss = (if \<forall>s \<in> ss. dom a s \<in> sf (a#as) s u
                                     then a # gen_purgx sf u as (\<Union>s \<in> ss. {s'. (s,s') \<in> Step a})
                                     else gen_purgx sf u as ss)"

definition xpurge :: "'d \<Rightarrow> 'e list \<Rightarrow> 's set \<Rightarrow> 'e list" where
  "xpurge \<equiv> gen_purge xources"

definition ipurgx :: "'d \<Rightarrow> 'e list \<Rightarrow> 's set \<Rightarrow> 'e list" where
  "ipurgx \<equiv> gen_purgx sources"

definition xpurgx :: "'d \<Rightarrow> 'e list \<Rightarrow> 's set \<Rightarrow> 'e list" where
  "xpurgx \<equiv> gen_purgx xources"

lemma xpurge_Nil:
  "xpurge u [] ss = []"
  by (auto simp: xpurge_def)

lemma ipurgx_Nil:
  "ipurgx u [] ss = []"
  by (auto simp: ipurgx_def)

lemma xpurgx_Nil:
  "xpurgx u [] ss = []"
  by (auto simp: xpurgx_def)

lemma xpurge_Cons:
  "xpurge u (a # as) ss = (if \<exists>s \<in> ss. dom a s \<in> xources (a # as) s u
                           then a # xpurge u as (\<Union>s\<in>ss. {s'. (s,s') \<in> Step a})
                           else xpurge u as ss)"
  by (auto simp: xpurge_def)

lemma ipurgx_Cons:
  "ipurgx u (a # as) ss = (if (\<forall>s\<in>ss. dom a s \<in> sources (a # as) s u)
                           then a # ipurgx u as (\<Union>s \<in> ss. {s'. (s,s') \<in> Step a})
                           else ipurgx u as ss)"
  by (auto simp: ipurgx_def)

lemma xpurgx_Cons:
  "xpurgx u (a # as) ss = (if (\<forall>s\<in>ss. dom a s \<in> xources (a # as) s u)
                           then a # xpurgx u as (\<Union>s\<in>ss. {s'. (s,s') \<in> Step a})
                           else xpurgx u as ss)"
  by (auto simp: xpurgx_def)

definition xNonleakage_gen :: bool where
  "xNonleakage_gen \<equiv> \<forall>as s u t. reachable s \<and> reachable t
                                 \<longrightarrow> s \<sim>schedDomain\<sim> t
                                 \<longrightarrow> s \<approx>(xources as s u)\<approx> t
                                 \<longrightarrow> uwr_equiv s as t as u"

end


context unwinding_system begin

lemma xources_sources:
  "confidentiality_u \<Longrightarrow> reachable s \<longrightarrow> (xources as s u = sources as s u)"
  apply (induct as arbitrary: s)
   apply (simp add: xources_Nil sources_Nil)
  apply (simp add: sources_Cons xources_Cons)
  apply (rule impI)
  apply (rule un_eq)
   apply (rule sym)
   apply (simp only: Union_eq, simp only: UNION_eq[symmetric])
   apply (simp only: Inter_eq, simp only: INTER_eq[symmetric])
   apply (rule Un_eq_Int)
     apply (clarsimp simp: Step_def)
     apply (erule reachable_enabled)
    apply (clarsimp simp: Step_def)
    apply (erule reachable_enabled)
   apply clarsimp
   apply (drule_tac x=s'a in meta_spec, clarsimp simp: reachable_Step)
   apply (rule sources_eq)
      apply assumption
     apply (fastforce intro: sched_equiv_preserved uwr_refl)
    apply (fastforce intro: reachable_Step)
   apply (fastforce intro: reachable_Step)
  apply (rule Collect_cong)
  apply (rule conj_cong, rule refl)
  apply safe
   apply (cut_tac s=s and a=a in enabled_Step)
    apply assumption
   apply clarsimp
   apply (drule_tac x=s' in spec)
   apply clarsimp
   apply (rule_tac x=v in exI)
   apply clarsimp
   apply (rule_tac x=s' in exI)
   apply (drule_tac x=s' in meta_spec)
   apply (fastforce intro: reachable_Step)
  apply (rule_tac x=v in exI, clarsimp)
  apply (drule_tac x=s' in meta_spec)
  apply (clarsimp simp: reachable_Step)
  apply (rule subst[OF sources_eq])
      apply assumption
     prefer 4
     apply assumption
    apply (fastforce intro: sched_equiv_preserved uwr_refl)
  by (auto intro: reachable_Step)

lemma xpurge_ipurge':
  "confidentiality_u
   \<Longrightarrow> (\<forall>s\<in>ss. reachable s) \<longrightarrow> xpurge u as ss = ipurge u as ss"
  apply (induct as arbitrary: ss)
   apply (simp add: xpurge_Nil ipurge_Nil)
  apply (clarsimp simp: ipurge_Cons xpurge_Cons xources_sources[rule_format] intro: reachable_Step
         | safe)+
  apply (drule_tac x="\<Union>s\<in>ss. {s'. (s,s') \<in> Step a}" in meta_spec)
  apply (fastforce intro: reachable_Step)
  done

lemma ipurgx_xpurge':
  "confidentiality_u
   \<Longrightarrow> (\<forall>s\<in>ss. reachable s) \<and> (\<exists>s. s \<in> ss) \<and> (\<forall>s s'. s\<in>ss \<and> s'\<in>ss \<longrightarrow> s\<sim>schedDomain\<sim>s')
       \<longrightarrow> ipurgx u as ss = xpurge u as ss"
  apply (induct as arbitrary: ss)
   apply (simp add: ipurgx_Nil xpurge_Nil)
  apply (clarsimp simp: xpurge_Cons ipurgx_Cons | safe)+
    apply (drule_tac x="\<Union>s\<in>ss. {s'. (s,s') \<in> Step a}" in meta_spec)
    apply (erule impE)
     apply (rule conjI)
      apply (fastforce intro: reachable_Step)
     apply (rule conjI)
      apply (drule bspec, assumption, frule_tac a=a in enabled_Step)
      apply blast
     apply clarsimp
     apply (match conclusion in \<open>s' \<sim>schedDomain\<sim> t'\<close> for s' t' \<Rightarrow>
             \<open>match premises in \<open>(s,s') \<in> Step a\<close> and \<open>(t,t') \<in> Step a\<close> for a s t \<Rightarrow>
                \<open>rule sched_equiv_preserved[of s t]\<close>\<close>)
          apply assumption
         apply blast
        apply blast
       apply blast
      apply assumption
     apply assumption
    apply assumption
   apply (simp add: xources_sources)
  apply (simp add: xources_sources)
  apply (erule notE)
  apply (frule_tac s=s and t=sa in sources_eq, simp+)
  apply (erule ssubst)
  apply (subst schedIncludesCurrentDom)
   prefer 2
   apply assumption
  apply blast
  done

lemma ipurgx_xpurgx':
  "confidentiality_u \<Longrightarrow> (\<forall>s\<in>ss. reachable s) \<longrightarrow> ipurgx u as ss = xpurgx u as ss"
  apply (induct as arbitrary: ss)
   apply (simp add: ipurgx_Nil xpurgx_Nil)
  apply (clarsimp simp: xpurgx_Cons ipurgx_Cons | safe)+
    apply (drule_tac x="\<Union>s\<in>ss. {s'. (s,s') \<in> Step a}" in meta_spec)
    apply (fastforce intro: reachable_Step)
   apply (simp add: xources_sources)
  apply (simp add: xources_sources)
  done

lemma xpurge_ipurge:
  "\<lbrakk> confidentiality_u; reachable s \<rbrakk>
     \<Longrightarrow> xpurge u as {s} = ipurge u as {s}"
  by (subst xpurge_ipurge', auto)

lemma ipurgx_ipurge:
  "\<lbrakk> confidentiality_u; reachable s \<rbrakk>
     \<Longrightarrow> ipurgx u as {s} = ipurge u as {s}"
  apply (subst ipurgx_xpurge', (simp add: uwr_refl)+)
  apply (subst xpurge_ipurge', auto)
  done

lemma xpurgx_ipurge:
  "\<lbrakk> confidentiality_u; reachable s \<rbrakk>
     \<Longrightarrow> xpurgx u as {s} = ipurge u as {s}"
  apply (subst ipurgx_xpurgx'[rule_format, THEN sym], simp+)
  apply (subst ipurgx_xpurge', (simp add: uwr_refl)+)
  apply (subst xpurge_ipurge', auto)
  done

(* we have four different purge functions, and two different sources functions.
   So we should be able to make 8 different definitions of security. All of which
   are equivalent. One of those definitions is of course the one above. *)
definition xNoninfluence_strong_uwr_xources_ipurge :: bool where
  "xNoninfluence_strong_uwr_xources_ipurge \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                                            \<longrightarrow> s \<approx>(xources as s u)\<approx> t
                                                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                                                            \<longrightarrow> ipurge u as {s} = ipurge u bs {s}
                                                            \<longrightarrow> uwr_equiv s as t bs u"

definition xNoninfluence_strong_uwr_sources_xpurge :: bool where
  "xNoninfluence_strong_uwr_sources_xpurge \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                                            \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                                                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                                                            \<longrightarrow> xpurge u as {s} = xpurge u bs {s}
                                                            \<longrightarrow> uwr_equiv s as t bs u"

definition xNoninfluence_strong_uwr_xources_xpurge :: bool where
  "xNoninfluence_strong_uwr_xources_xpurge \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                                            \<longrightarrow> s \<approx>(xources as s u)\<approx> t
                                                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                                                            \<longrightarrow> xpurge u as {s} = xpurge u bs {s}
                                                            \<longrightarrow> uwr_equiv s as t bs u"

definition xNoninfluence_strong_uwr_sources_ipurgx :: bool where
  "xNoninfluence_strong_uwr_sources_ipurgx \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                                            \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                                                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                                                            \<longrightarrow> ipurgx u as {s} = ipurgx u bs {s}
                                                            \<longrightarrow> uwr_equiv s as t bs u"

definition
  xNoninfluence_strong_uwr_xources_ipurgx :: bool where
  "xNoninfluence_strong_uwr_xources_ipurgx \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                                            \<longrightarrow> s \<approx>(xources as s u)\<approx> t
                                                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                                                            \<longrightarrow> ipurgx u as {s} = ipurgx u bs {s}
                                                            \<longrightarrow> uwr_equiv s as t bs u"

definition xNoninfluence_strong_uwr_sources_xpurgx :: bool where
  "xNoninfluence_strong_uwr_sources_xpurgx \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                                            \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                                                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                                                            \<longrightarrow> xpurgx u as {s} = xpurgx u bs {s}
                                                            \<longrightarrow> uwr_equiv s as t bs u"

definition xNoninfluence_strong_uwr_xources_xpurgx :: bool where
  "xNoninfluence_strong_uwr_xources_xpurgx \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                                            \<longrightarrow> s \<approx>(xources as s u)\<approx> t
                                                            \<longrightarrow> s \<sim>schedDomain\<sim> t
                                                            \<longrightarrow> xpurgx u as {s} = xpurgx u bs {s}
                                                            \<longrightarrow> uwr_equiv s as t bs u"

(* The following perhaps feels more natural, but we show is equivalent.
   'pg' here is for Pete Gammie who pushed me to prove this. *)
definition Noninfluence_strong_uwr_pg :: bool where
  "Noninfluence_strong_uwr_pg \<equiv> \<forall>u as bs s t. reachable s \<and> reachable t
                                               \<longrightarrow> s \<approx>(sources as s u)\<approx> t
                                               \<longrightarrow> s \<sim>schedDomain\<sim> t
                                               \<longrightarrow> ipurge u as {s} = ipurge u bs {t}
                                               \<longrightarrow> uwr_equiv s as t bs u"

lemma xNoninfluence_strong_uwr_xources_ipurge_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> xNoninfluence_strong_uwr_xources_ipurge = Noninfluence_strong_uwr"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_ipurge_def Noninfluence_strong_uwr_def)
  apply (frule (1) confidentiality_u_weak)
  apply (simp add: xources_sources)
  done

lemma xNoninfluence_strong_uwr_sources_xpurge_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> xNoninfluence_strong_uwr_sources_xpurge = Noninfluence_strong_uwr"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_xpurge_def Noninfluence_strong_uwr_def)
  apply (frule (1) confidentiality_u_weak)
  apply (simp add: xpurge_ipurge)
  done

lemma xNoninfluence_strong_uwr_xources_xpurge_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
    \<Longrightarrow> xNoninfluence_strong_uwr_xources_xpurge = Noninfluence_strong_uwr"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_xpurge_def Noninfluence_strong_uwr_def)
  apply (frule (1) confidentiality_u_weak)
  apply (simp add: xources_sources xpurge_ipurge)
  done

lemma xNoninfluence_strong_uwr_sources_ipurgx_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> xNoninfluence_strong_uwr_sources_ipurgx = Noninfluence_strong_uwr"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_ipurgx_def Noninfluence_strong_uwr_def)
  apply (frule (1) confidentiality_u_weak)
  apply (simp add: ipurgx_ipurge)
  done

lemma xNoninfluence_strong_uwr_xources_ipurgx_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> xNoninfluence_strong_uwr_xources_ipurgx = Noninfluence_strong_uwr"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_ipurgx_def Noninfluence_strong_uwr_def)
  apply (frule (1) confidentiality_u_weak)
  apply (simp add: xources_sources ipurgx_ipurge)
  done

lemma xNoninfluence_strong_uwr_sources_xpurgx_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> xNoninfluence_strong_uwr_sources_xpurgx = Noninfluence_strong_uwr"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_xpurgx_def Noninfluence_strong_uwr_def)
  apply (frule (1) confidentiality_u_weak)
  apply (simp add: xpurgx_ipurge)
  done

lemma xNoninfluence_strong_uwr_xources_xpurgx_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> xNoninfluence_strong_uwr_xources_xpurgx = Noninfluence_strong_uwr"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_xpurgx_def Noninfluence_strong_uwr_def)
  apply (frule (1) confidentiality_u_weak)
  apply (simp add: xpurgx_ipurge xources_sources)
  done

lemma Noninfluence_strong_uwr_pg_Noninfluence_strong_uwr:
  "\<lbrakk> confidentiality_u_weak; integrity_u \<rbrakk>
     \<Longrightarrow> Noninfluence_strong_uwr_pg = Noninfluence_strong_uwr"
  apply (clarsimp simp: Noninfluence_strong_uwr_pg_def Noninfluence_strong_uwr_def)
  apply (frule (1) confidentiality_u_weak)
  apply (simp add: ipurge_eq)
  done

lemma xources_Step:
  "\<lbrakk> reachable s; (dom a s, u) \<notin> policy \<rbrakk> \<Longrightarrow> xources [a] s u = {u}"
  by (auto simp: xources_Cons xources_Nil enabled_Step dest: enabled_Step)

lemma xources_Step_2:
  "\<lbrakk> reachable s; (dom a s, u) \<in> policy \<rbrakk> \<Longrightarrow> xources [a] s u = {dom a s,u}"
  by (auto simp: xources_Cons xources_Nil enabled_Step dest: enabled_Step)

lemma xNoninfluence_strong_uwr_xources_ipurge_confidentiality_u_weak:
  "xNoninfluence_strong_uwr_xources_ipurge \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_ipurge_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: xources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done

lemma xNoninfluence_strong_uwr_sources_xpurge_confidentiality_u_weak:
  "xNoninfluence_strong_uwr_sources_xpurge \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_xpurge_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: sources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done

lemma xNoninfluence_strong_uwr_xources_xpurge_confidentiality_u_weak:
  "xNoninfluence_strong_uwr_xources_xpurge \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_xpurge_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: xources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done

lemma xNoninfluence_strong_uwr_sources_ipurgx_confidentiality_u_weak:
  "xNoninfluence_strong_uwr_sources_ipurgx \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_ipurgx_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: sources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done

lemma xNoninfluence_strong_uwr_xources_ipurgx_confidentiality_u_weak:
  "xNoninfluence_strong_uwr_xources_ipurgx \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_ipurgx_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: xources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done

lemma xNoninfluence_strong_uwr_sources_xpurgx_confidentiality_u_weak:
  "xNoninfluence_strong_uwr_sources_xpurgx \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_xpurgx_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: sources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done

lemma xNoninfluence_strong_uwr_xources_xpurgx_confidentiality_u_weak:
  "xNoninfluence_strong_uwr_xources_xpurgx \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_xpurgx_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: xources_Step_2 sameFor_dom_def uwr_equiv_def Step_def)
  done

lemma ipurge_single_eq:
  "\<lbrakk> reachable s; reachable t; s \<sim>schedDomain\<sim> t \<rbrakk>
     \<Longrightarrow> ipurge u [a] {s} = ipurge u [a] {t}"
  apply (frule_tac e=a in schedIncludesCurrentDom)
  apply (simp add: ipurge_Cons ipurge_Nil sources_Cons sources_Nil)
  apply (auto dest: enabled_Step)
  done

lemma Noninfluence_strong_uwr_pg_confidentiality_u_weak:
  "Noninfluence_strong_uwr_pg \<Longrightarrow> confidentiality_u_weak"
  apply (clarsimp simp: Noninfluence_strong_uwr_pg_def confidentiality_u_weak_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[a]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=t in spec)
  apply (simp add: sources_Step_2 sameFor_dom_def uwr_equiv_def Step_def ipurge_single_eq)
  done

end


context complete_unwinding_system begin

lemma Nonleakage_gen_xNonleakage_gen:
  "confidentiality_u \<Longrightarrow> Nonleakage_gen = xNonleakage_gen"
  apply (simp add: Nonleakage_gen_def xNonleakage_gen_def)
  apply (fastforce simp: xources_sources)
  done

lemma xNonleakage_gen:
  "confidentiality_u \<Longrightarrow> xNonleakage_gen"
  apply (simp add: Nonleakage_gen_xNonleakage_gen[symmetric])
  apply (erule Nonleakage_gen)
  done

lemma xNonleakage_gen_confidentiality_u:
  "xNonleakage_gen \<Longrightarrow> confidentiality_u"
  apply (clarsimp simp: xNonleakage_gen_def confidentiality_u_def)
  apply (drule_tac x="[a]" in spec, drule_tac x=s in spec)
  apply (drule_tac x=u in spec, drule_tac x=t in spec)
  apply (case_tac "dom a s \<leadsto> u")
   apply (simp add: xources_Step_2 uwr_equiv_def sameFor_dom_def Step_def)
  apply (simp add: xources_Step uwr_equiv_def sameFor_dom_def Step_def)
  done

lemma xNoninfluence_strong_uwr_xources_ipurge_integrity_u:
  "xNoninfluence_strong_uwr_xources_ipurge \<Longrightarrow> integrity_u"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_ipurge_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: sources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def ipurge_Cons ipurge_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

lemma xNoninfluence_strong_uwr_sources_xpurge_integrity_u:
  "xNoninfluence_strong_uwr_sources_xpurge \<Longrightarrow> integrity_u"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_xpurge_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: xources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def xpurge_Cons xpurge_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

lemma xNoninfluence_strong_uwr_xources_xpurge_integrity_u:
  "xNoninfluence_strong_uwr_xources_xpurge \<Longrightarrow> integrity_u"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_xpurge_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: xources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def xpurge_Cons xpurge_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

lemma xNoninfluence_strong_uwr_sources_ipurgx_integrity_u:
  "xNoninfluence_strong_uwr_sources_ipurgx \<Longrightarrow> integrity_u"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_ipurgx_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: sources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def ipurgx_Cons ipurgx_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

lemma xNoninfluence_strong_uwr_xources_ipurgx_integrity_u:
  "xNoninfluence_strong_uwr_xources_ipurgx \<Longrightarrow> integrity_u"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_ipurgx_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: sources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def ipurgx_Cons ipurgx_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

lemma xNoninfluence_strong_uwr_sources_xpurgx_integrity_u:
  "xNoninfluence_strong_uwr_sources_xpurgx \<Longrightarrow> integrity_u"
  apply (clarsimp simp: xNoninfluence_strong_uwr_sources_xpurgx_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: xources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def xpurgx_Cons xpurgx_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

lemma xNoninfluence_strong_uwr_xources_xpurgx_integrity_u:
  "xNoninfluence_strong_uwr_xources_xpurgx \<Longrightarrow> integrity_u"
  apply (clarsimp simp: xNoninfluence_strong_uwr_xources_xpurgx_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: xources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def xpurgx_Cons xpurgx_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

lemma Noninfluence_strong_uwr_pg_integrity_u:
  "Noninfluence_strong_uwr_pg \<Longrightarrow> integrity_u"
  apply (clarsimp simp: Noninfluence_strong_uwr_pg_def integrity_u_def)
  apply (drule_tac x=u in spec, drule_tac x="[a]" in spec, drule_tac x="[]" in spec)
  apply (drule_tac x=s in spec, drule_tac x=s in spec)
  apply (simp add: sources_Step sameFor_dom_def uwr_refl
                   uwr_equiv_def Step_def ipurge_Cons ipurge_Nil
            split: if_splits)
   apply (simp add: policy_refl)
  apply (simp add: execution_Nil)
  apply (blast intro: uwr_sym)
  done

(* The choice as to which sources/ipurge definition to adopt doesn't matter.
   For this reason we adopt the one that is simpler to prove the sufficiency of the
   unwinding conditions for, while having both the sources and ipurge being of the
   same "kind". *)
lemma Noninfluence_strong_uwr_equiv_xNoninfluence_strong_uwr_xources_ipurge:
  "Noninfluence_strong_uwr = xNoninfluence_strong_uwr_xources_ipurge"
  apply (rule iffI)
   apply (subst xNoninfluence_strong_uwr_xources_ipurge_Noninfluence_strong_uwr)
     apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_integrity_u)
   apply assumption
  apply (rule Noninfluence_strong_uwr)
   apply (erule xNoninfluence_strong_uwr_xources_ipurge_confidentiality_u_weak)
  apply (erule xNoninfluence_strong_uwr_xources_ipurge_integrity_u)
  done

lemma Noninfluence_strong_uwr_equiv_xNoninfluence_strong_uwr_sources_xpurge:
  "Noninfluence_strong_uwr = xNoninfluence_strong_uwr_sources_xpurge"
  apply (rule iffI)
   apply (subst xNoninfluence_strong_uwr_sources_xpurge_Noninfluence_strong_uwr)
     apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_integrity_u)
   apply assumption
  apply (rule Noninfluence_strong_uwr)
   apply (erule xNoninfluence_strong_uwr_sources_xpurge_confidentiality_u_weak)
  apply (erule xNoninfluence_strong_uwr_sources_xpurge_integrity_u)
  done

lemma Noninfluence_strong_uwr_equiv_xNoninfluence_strong_uwr_xources_xpurge:
  "Noninfluence_strong_uwr = xNoninfluence_strong_uwr_xources_xpurge"
  apply (rule iffI)
   apply (subst xNoninfluence_strong_uwr_xources_xpurge_Noninfluence_strong_uwr)
     apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_integrity_u)
   apply assumption
  apply (rule Noninfluence_strong_uwr)
   apply (erule xNoninfluence_strong_uwr_xources_xpurge_confidentiality_u_weak)
  apply (erule xNoninfluence_strong_uwr_xources_xpurge_integrity_u)
  done

lemma Noninfluence_strong_uwr_equiv_xNoninfluence_strong_uwr_sources_ipurgx:
  "Noninfluence_strong_uwr = xNoninfluence_strong_uwr_sources_ipurgx"
  apply (rule iffI)
   apply (subst xNoninfluence_strong_uwr_sources_ipurgx_Noninfluence_strong_uwr)
     apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_integrity_u)
   apply assumption
  apply (rule Noninfluence_strong_uwr)
   apply (erule xNoninfluence_strong_uwr_sources_ipurgx_confidentiality_u_weak)
  apply (erule xNoninfluence_strong_uwr_sources_ipurgx_integrity_u)
  done

lemma Noninfluence_strong_uwr_equiv_xNoninfluence_strong_uwr_xources_ipurgx:
  "Noninfluence_strong_uwr = xNoninfluence_strong_uwr_xources_ipurgx"
  apply (rule iffI)
   apply (subst xNoninfluence_strong_uwr_xources_ipurgx_Noninfluence_strong_uwr)
     apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_integrity_u)
   apply assumption
  apply (rule Noninfluence_strong_uwr)
   apply (erule xNoninfluence_strong_uwr_xources_ipurgx_confidentiality_u_weak)
  apply (erule xNoninfluence_strong_uwr_xources_ipurgx_integrity_u)
  done

lemma Noninfluence_strong_uwr_equiv_xNoninfluence_strong_uwr_sources_xpurgx:
  "Noninfluence_strong_uwr = xNoninfluence_strong_uwr_sources_xpurgx"
  apply (rule iffI)
   apply (subst xNoninfluence_strong_uwr_sources_xpurgx_Noninfluence_strong_uwr)
     apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_integrity_u)
   apply assumption
  apply (rule Noninfluence_strong_uwr)
   apply (erule xNoninfluence_strong_uwr_sources_xpurgx_confidentiality_u_weak)
  apply (erule xNoninfluence_strong_uwr_sources_xpurgx_integrity_u)
  done

lemma Noninfluence_strong_uwr_equiv_xNoninfluence_strong_uwr_xources_xpurgx:
  "Noninfluence_strong_uwr = xNoninfluence_strong_uwr_xources_xpurgx"
  apply (rule iffI)
   apply (subst xNoninfluence_strong_uwr_xources_xpurgx_Noninfluence_strong_uwr)
     apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_integrity_u)
   apply assumption
  apply (rule Noninfluence_strong_uwr)
   apply (erule xNoninfluence_strong_uwr_xources_xpurgx_confidentiality_u_weak)
  apply (erule xNoninfluence_strong_uwr_xources_xpurgx_integrity_u)
  done

lemma Noninfluence_strong_uwr_equiv_Noninfluence_strong_uwr_pg:
  "Noninfluence_strong_uwr = Noninfluence_strong_uwr_pg"
  apply (rule iffI)
   apply (subst Noninfluence_strong_uwr_pg_Noninfluence_strong_uwr)
     apply (erule Noninfluence_strong_uwr_confidentiality_u_weak)
    apply (erule Noninfluence_strong_uwr_integrity_u)
   apply assumption
  apply (rule Noninfluence_strong_uwr)
   apply (erule Noninfluence_strong_uwr_pg_confidentiality_u_weak)
  apply (erule Noninfluence_strong_uwr_pg_integrity_u)
  done

end

end
