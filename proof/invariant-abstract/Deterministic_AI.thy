(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Deterministic_AI
imports AInvs
begin

context begin interpretation Arch .
requalify_facts
  update_work_units_empty_fail
  reset_work_units_empty_fail
  set_domain_empty_fail
  thread_set_domain_empty_fail
  arch_post_cap_deletion_valid_list
end

lemmas [wp] =
  update_work_units_empty_fail
  reset_work_units_empty_fail
  set_domain_empty_fail
  thread_set_domain_empty_fail

declare dxo_wp_weak[wp del]

(** This theory shows that the cdt_list operations
        correctly correspond to the existing cdt operations
        and demonstrates their effect on the traversal order
        of the tree. *)

(* An unspecified invariant is given from the state
        extension's type class, which is assumed to hold over
        all the capability operations. We show here that it
        therefore holds over the whole kernel. This will
        later be instantiated to valid_list. *)

(* a valid cdt_list for a node is a list that contains all of its children
        (from the mdb) exactly once *)

 (*Some nasty hackery to get around lack of polymorphic type class operations*)

lemma and_assoc: "(A and (B and C)) = (A and B and C)"
  apply (rule ext)
  apply simp
done

lemma no_children_empty_desc:
  "(\<forall>c. m c \<noteq> Some slot) = (descendants_of slot m = {})"
  apply(rule iffI)
   apply(simp add: descendants_of_def cdt_parent_defs)
   apply(intro allI notI)
   apply(drule tranclD)
   apply(simp)
  apply(fastforce simp: descendants_of_def cdt_parent_defs)
  done

lemma next_childD:
  "\<lbrakk>next_child slot t = Some child; valid_list_2 t m\<rbrakk>
   \<Longrightarrow> (\<exists>xs. t slot = child # xs) \<and> m child = Some slot"
  apply(simp only: valid_list_2_def)
  apply(erule conjE)
  apply(erule_tac x=slot in allE)
  apply(clarsimp simp: next_child_def valid_list_2_def)
  apply(case_tac "t slot")
   apply(simp)
  apply(fastforce)
  done

lemma next_child_NoneD:
  notes split_paired_All[simp del]
  shows "next_child slot t = None \<Longrightarrow> t slot = []"
  apply(simp add: next_child_def)
  apply(case_tac "t slot")
   apply(simp)
  apply(simp)
  done

lemma next_child_None_empty_desc:
  notes split_paired_All[simp del]
  shows "valid_list_2 t m
    \<Longrightarrow> (next_child slot t = None) = (descendants_of slot m = {})"
  apply(simp add: valid_list_2_def)
  apply(erule conjE)
  apply(erule_tac x=slot in allE)
  apply(clarsimp simp: next_child_def)
  apply(case_tac "t slot")
   apply(simp add: no_children_empty_desc)
  apply(fastforce simp: descendants_of_def cdt_parent_defs)
  done

lemma next_sibD:
  "next_sib slot t m = Some child
   \<Longrightarrow> (\<exists>p. m slot = Some p \<and> after_in_list (t p) slot = Some child)"
  apply(clarsimp simp: next_sib_def)
  apply(case_tac "m slot")
   apply(simp)
  apply(clarsimp)
  done

lemma next_sib_NoneD:
  "next_sib slot t m = None
   \<Longrightarrow> m slot = None \<or> (\<exists>p. m slot = Some p \<and> after_in_list (t p) slot = None)"
  apply(clarsimp simp: next_sib_def)
  apply(case_tac "m slot")
   apply(fastforce)+
   done

lemma desc_not_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "valid_mdb s \<Longrightarrow> slot \<notin> descendants_of slot (cdt s)"
  apply(fastforce simp: valid_mdb_def no_mloop_def descendants_of_def cdt_parent_defs)
  done

lemma next_childI:
  "t slot = child # xs
  \<Longrightarrow> next_child slot t = Some child"
  by (simp add: next_child_def)

lemma next_childI':
  "\<lbrakk>t slot = child # xs; x = Some child\<rbrakk>
  \<Longrightarrow> next_child slot t = x"
  by (simp add: next_child_def)

lemma next_sibI:
  "\<lbrakk>m slot = Some p; after_in_list (t p) slot = Some sib\<rbrakk>
  \<Longrightarrow> next_sib slot t m = Some sib"
  by (simp add: next_sib_def)

lemma next_sibI':
  "\<lbrakk>m slot = Some p; after_in_list (t p) slot = Some sib; x = Some sib\<rbrakk>
  \<Longrightarrow> next_sib slot t m = x"
  by (simp add: next_sib_def)

lemma next_child_NoneI:
  "t slot = [] \<Longrightarrow> next_child slot t = None"
  by (simp add: next_child_def)

lemma next_sib_NoneI:
  "m slot = None \<or> (m slot = Some p \<and> after_in_list (t p) slot = None) \<Longrightarrow> next_sib slot t m = None"
  by (fastforce simp: next_sib_def)

lemma not_child_not_sib:
  "\<lbrakk>m slot = None; valid_list_2 t m\<rbrakk> \<Longrightarrow> next_sib p t m \<noteq> Some slot"
  apply(simp add: next_sib_def)
  apply(case_tac "m p")
   apply(simp)
  apply(simp)
  apply(rule notI)
  apply(simp only: valid_list_2_def)
  apply(erule conjE)
  apply(erule_tac x=a in allE)
  apply(fastforce dest: after_in_list_in_list)
  done

lemma not_child_no_sibs:
  "m slot = None \<Longrightarrow> next_sib slot t m = None"
  by (simp add: next_sib_def)

lemma descendants_linear:
  "\<lbrakk>a \<in> descendants_of b m; a \<in> descendants_of c m; b \<noteq> c\<rbrakk>
    \<Longrightarrow> b \<in> descendants_of c m \<or> c \<in> descendants_of b m"
  apply(clarsimp)
  apply(simp add: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)
  apply(induct b a rule: trancl.induct)
   apply(simp)
   apply(erule tranclE)
    apply(simp)
   apply(simp)
  apply(simp)
  apply(subgoal_tac "(c, b) \<in> {(p, c). m c = Some p}\<^sup>+")
   apply(simp)
  apply(subgoal_tac "b \<noteq> c")
   apply(erule_tac a=c and b=ca in tranclE)
    apply(simp)
   apply(simp)
  apply(fastforce)
  done

lemma descendants_trans:
  "\<lbrakk>a \<in> descendants_of b m; b \<in> descendants_of c m\<rbrakk> \<Longrightarrow> a \<in> descendants_of c m"
  by (simp add: descendants_of_def)

definition finite_depth :: "cdt \<Rightarrow> bool" where
  "finite_depth m \<equiv>
    \<forall>slot. \<exists>p. (slot \<in> descendants_of p m \<or> p = slot) \<and> m p = None"

lemma sib_not_desc:
  "\<lbrakk>no_mloop m; m x = Some p; m y = Some p\<rbrakk>
    \<Longrightarrow> x \<notin> descendants_of y m"
  apply(rule notI)
  apply(simp add: descendants_of_def cdt_parent_defs)
  apply(drule tranclD2)
  apply(elim conjE exE)
  apply(simp)
  apply(drule rtranclD)
  apply(erule disjE)
   apply(fastforce simp: no_mloop_def cdt_parent_defs)
  apply(erule conjE)
  apply(subgoal_tac "(z, z) \<in> {(p, c). m c = Some p}\<^sup>+")
   prefer 2
   apply(rule_tac b=y in trancl_into_trancl2)
    apply(simp)
   apply(simp)
  apply(fastforce simp: no_mloop_def cdt_parent_defs)
  done

lemma finite_depth:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "valid_mdb s \<Longrightarrow> finite_depth (cdt s)"
  apply(simp add: finite_depth_def)
  apply(intro allI)
  apply(subgoal_tac "{x. slot \<in> descendants_of x (cdt s)} \<subseteq> {x. cte_wp_at (\<lambda>_. True) x s}")
   prefer 2
   apply(fastforce simp: descendants_of_cte_at2)
  apply(drule finite_subset)
   apply(simp add: cte_wp_at_set_finite)
  apply(case_tac "cdt s slot")
   apply(fastforce)
  apply(rule ccontr)
  apply(simp)
  apply(frule_tac f="\<lambda>x. THE y. cdt s x = Some y" in inj_on_iff_eq_card)
  apply(subgoal_tac "inj_on (\<lambda>x. THE y. cdt s x = Some y) {x. slot \<in> descendants_of x (cdt s)}")
   prefer 2
   apply(simp(no_asm) add: inj_on_def)
   apply(intro allI impI)
   apply(rule ccontr)
   apply(frule_tac b=x and c=y in descendants_linear)
     apply(simp)
    apply(simp)
   apply(case_tac "cdt s x")
    apply(fastforce)
   apply(case_tac "cdt s y")
    apply(fastforce)
   apply(fastforce simp: valid_mdb_def sib_not_desc)
  apply(simp)
  apply(subgoal_tac "((\<lambda>x. THE y. cdt s x = Some y) ` {x. slot \<in> descendants_of x (cdt s)})
                      \<subset> {x. slot \<in> descendants_of x (cdt s)}")
   prefer 2
   apply(rule psubsetI)
    apply(rule subsetI)
    apply(simp)
    apply(erule imageE)
    apply(case_tac "cdt s xa")
     apply(fastforce)
    apply(rule_tac b=xa in descendants_trans)
     apply(simp)
    apply(fastforce simp: descendants_of_def cdt_parent_defs)
   apply(rule_tac x=a in set_neqI[symmetric])
    apply(fastforce simp: descendants_of_def cdt_parent_defs)
   apply(rule notI)
   apply(erule imageE)
   apply(case_tac "cdt s x")
    apply(fastforce)
   apply(fastforce simp: sib_not_desc valid_mdb_def)
  apply(drule psubset_card_mono)
   apply(assumption)
  apply(simp)
  done

lemma cdt_power:
  "\<lbrakk>\<forall>i. m (f i) = Some (f (Suc i)); (p, f 0) \<in> {(p, c). m c = Some p} ^^ n\<rbrakk>
    \<Longrightarrow> p = f n"
  apply(induct n arbitrary: p)
   apply(simp)
  apply (metis (lifting, full_types) mem_Collect_eq option.inject prod.simps(2) relpow_Suc_D2)
  done

lemma wf_cdt_parent_rel:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "finite_depth m \<Longrightarrow> wf (cdt_parent_rel m)"
  apply(subst wf_iff_no_infinite_down_chain)
  apply(rule notI)
  apply(clarsimp simp: finite_depth_def descendants_of_def cdt_parent_defs)
  apply(erule_tac x="f 0" in allE)
  apply(elim exE conjE)
  apply(erule disjE)
   apply(simp add: trancl_power)
   apply(elim exE conjE)
   apply(frule cdt_power)
    apply(assumption)
   apply(clarsimp)
  apply(simp)
  done

lemma cdt_induct:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>\<And>x. m x = None \<Longrightarrow> P x; \<And>x y. \<lbrakk>m x = Some y; P y\<rbrakk> \<Longrightarrow> P x; finite_depth m\<rbrakk>
    \<Longrightarrow> P slot"
  apply(induct_tac rule: wf_induct[where r="cdt_parent_rel m"])
   apply(simp add: wf_cdt_parent_rel)
  apply(simp add: cdt_parent_defs)
  apply(case_tac "m x")
   apply(simp)
  apply(erule_tac x=a in allE)
  apply(simp)
  done

lemma next_not_child_domintros:
  "(\<And>x. \<lbrakk>next_sib slot t m = None; m slot = Some x\<rbrakk>
    \<Longrightarrow> next_not_child_dom (x, t, m))
      \<Longrightarrow> next_not_child_dom (slot, t, m)"
  apply(rule accpI)
  apply(erule next_not_child_rel.cases)
  apply(simp)
  done

lemma next_not_child_termination:
  "finite_depth m \<Longrightarrow> next_not_child_dom (slot, t, m)"
  apply(induct_tac rule: cdt_induct[where m=m])
    apply(rule next_not_child_domintros)
    apply(simp)
   apply(rule next_not_child_domintros)
   apply(simp)
  apply(simp)
  done

lemma next_not_child_pinduct':
  "\<lbrakk>next_not_child_dom (slot, t, m);
   \<And>slot.
      \<lbrakk>next_not_child_dom (slot, t, m);
       \<And>a. \<lbrakk>next_sib slot t m = None; m slot = Some a\<rbrakk> \<Longrightarrow> P a t m\<rbrakk>
      \<Longrightarrow> P slot t m\<rbrakk>
  \<Longrightarrow> P slot t m"
  apply(induct rule: next_not_child.pinduct)
  apply(simp)
  done

lemma next_not_child_pinduct:
  "\<lbrakk>\<And>slot. \<lbrakk>\<And>a. \<lbrakk>next_sib slot t m = None; m slot = Some a\<rbrakk> \<Longrightarrow> P a\<rbrakk>
    \<Longrightarrow> P slot; finite_depth m\<rbrakk>
      \<Longrightarrow> P slot"
  apply(rule_tac t=t and m=m in next_not_child_pinduct')
   apply(rule next_not_child_termination)
   apply(assumption)
  apply(fastforce)
  done

declare next_not_child.psimps[simp]

lemma next_not_child_pinduct2':
  "\<lbrakk>next_not_child_dom (p, t, m);
  \<And>a slot. \<lbrakk>next_sib a t m = None; m a = Some slot; P a\<rbrakk> \<Longrightarrow> P slot;
  next_not_child p t m = Some n; P p;
  \<forall>a slot. next_sib a t m = Some slot \<longrightarrow> P slot\<rbrakk>
    \<Longrightarrow> P n"
  apply(induct rule: next_not_child.pinduct)
  apply(simp split: if_split_asm del: split_paired_All)
  apply(case_tac "m slot")
   apply simp
  apply simp
  done

lemma next_not_child_pinduct2:
  "\<lbrakk>\<And>a slot. \<lbrakk>next_sib a t m = None; m a = Some slot; P a\<rbrakk> \<Longrightarrow> P slot;
    next_not_child p t m = Some n; P p;
    \<forall>a slot. next_sib a t m = Some slot \<longrightarrow> P slot; finite_depth m\<rbrakk>
    \<Longrightarrow> P n"
  by (rule next_not_child_pinduct2', simp_all add: next_not_child_termination)

lemma next_not_child_linearI:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes f_d: "finite_depth m" shows
  "\<lbrakk>m p = m' p; next_sib p t m = next_sib p t' m';
     \<forall>q. p \<in> descendants_of q m \<longrightarrow> m q = m' q
     \<and> next_sib q t m = next_sib q t' m'; finite_depth m; finite_depth m'\<rbrakk>
    \<Longrightarrow> next_not_child p t' m' = next_not_child p t m"
  apply(induct rule: next_not_child_pinduct[where t=t and m=m])
   apply(simp)
   apply(case_tac "m slot")
    apply(simp add: next_not_child_termination)
   apply(case_tac "next_sib slot t m")
    apply(simp add: next_not_child_termination)
    apply(case_tac "m' slot")
     apply(simp)
    apply(simp)
    apply(atomize)
    apply(erule_tac x=aa in allE)
    apply(simp split: if_split_asm)
     apply(case_tac "m' aa")
      apply(simp)
      apply(simp add: next_not_child_termination)
      apply(intro conjI impI)
       apply(case_tac "m aa")
        apply(simp)
       apply(erule_tac x=aa in allE)
       apply(erule impE)
        apply(fastforce simp: cdt_parent_defs descendants_of_def)
       apply(simp)
      apply(erule exE)
      apply(erule_tac x=aa in allE)(* condense *)
      apply(erule impE)
       apply(fastforce simp: cdt_parent_defs descendants_of_def)
      apply(simp)
     apply(simp)
     apply(erule impE)
      apply(erule_tac x=aa in allE)
      apply(fastforce simp: cdt_parent_defs descendants_of_def)
     apply(erule impE)
      apply(erule_tac x=aa in allE)
      apply(fastforce simp: cdt_parent_defs descendants_of_def)
     apply(erule impE)
      apply(intro allI impI)
      apply(erule_tac x=q in allE)
      apply(erule impE)
       apply(simp add: cdt_parent_defs descendants_of_def)
       apply(rule_tac b=aa in trancl_into_trancl)
        apply(simp, simp)
      apply(simp)
     apply(erule_tac x= aa in allE)
     apply(erule impE)
      apply(fastforce simp: cdt_parent_defs descendants_of_def)
     apply(simp add: next_not_child_termination) (* condense *)
    apply(erule_tac x=aa in allE)
    apply(erule impE)
     apply(fastforce simp: cdt_parent_defs descendants_of_def)
    apply(simp add: next_not_child_termination)
   apply(simp)
   apply(fastforce simp: next_not_child_termination)
  using f_d
  apply(assumption)
  done

lemma next_not_child_linearI':
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes f_d: "finite_depth m" shows
  "\<lbrakk>finite_depth m'; m p = m' p; next_sib p t m = next_sib p t' m';
     \<forall>q. p \<in> descendants_of q m \<longrightarrow> m q = m' q
     \<and> (m q = m' q \<longrightarrow> next_sib q t m = next_sib q t' m')\<rbrakk>
    \<Longrightarrow> next_not_child p t' m' = next_not_child p t m"
  using f_d
  apply (rule next_not_child_linearI,simp+)
  done

lemma next_not_childI':
    notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes f_d: "finite_depth m" shows
  "\<lbrakk>next_sib p t m = Some n \<or>
   (next_sib p t m = None \<and>
     (\<exists>q. next_sib q t m = Some n \<and> p \<in> descendants_of q m
     \<and> (\<forall>q'. q' \<in> descendants_of q m \<and> p \<in> descendants_of q' m
        \<longrightarrow> next_sib q' t m = None))); finite_depth m\<rbrakk>
    \<Longrightarrow> next_not_child p t m = Some n"
  apply(induct p rule: next_not_child_pinduct[where t=t and m=m])
   apply(simp)
   apply(erule disjE)
    apply(simp add: next_not_child_termination)
   apply(simp)
   apply(elim conjE exE)
   apply(subst next_not_child.psimps, simp add: next_not_child_termination)
   apply(simp)
   apply(case_tac "m slot")
    apply(simp)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(drule tranclD2)
    apply(fastforce)
   apply(atomize)
   apply(erule_tac x=a in allE)
   apply(simp)
   apply(case_tac "next_sib a t m")
    apply(simp)
    apply(case_tac "a=q")
     apply(simp)
    apply(erule impE)
     apply(rule_tac x=q in exI)
     apply(simp add: descendants_of_def cdt_parent_defs)
     apply(drule tranclD2)
     apply(elim exE conjE, simp)
     apply(drule rtranclD, simp)
     apply(intro allI impI)
     apply(erule_tac x=q' in allE)
     apply(simp)
     apply(elim impE conjE)
      apply(drule_tac x=q' and y=z in tranclD2)
      apply(elim exE conjE)
      apply(simp)
      apply(rule_tac b=z in trancl_into_trancl)
       apply(rule_tac b=za in rtrancl_into_trancl1)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(simp)
    apply(simp)
   apply(simp)
   apply(case_tac "a=q")
    apply(simp)
   apply(erule_tac x=a in allE)
   apply(erule_tac Q="next_sib a t m = None" in impE)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(rule conjI)
    apply(drule tranclD2)
    apply(elim conjE exE)
    apply(simp)
    apply(drule rtranclD)
    apply(simp)
   apply(fastforce)
  apply(simp)
  using f_d apply(simp)
  done

lemma next_not_childI:
  "\<lbrakk>next_sib p t m = Some n \<or>
   (next_sib p t m = None \<and>
     (\<exists>q. next_sib q t m = Some n \<and> p \<in> descendants_of q m
     \<and> (\<forall>q'. q' \<in> descendants_of q m \<and> p \<in> descendants_of q' m
        \<longrightarrow> next_sib q' t m = None))); finite_depth m\<rbrakk>
    \<Longrightarrow> next_not_child p t m = Some n"
  by(simp add: next_not_childI')

lemma next_not_child_NoneI':
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes f_d: "finite_depth m"
  shows
  "\<lbrakk>\<forall>q. p \<in> descendants_of q m \<longrightarrow> next_sib q t m = None;
    next_sib p t m = None; finite_depth m\<rbrakk>
    \<Longrightarrow> next_not_child p t m = None"
  apply(induct p rule: next_not_child_pinduct[where t=t and m=m])
   apply(simp)
   apply(case_tac "m slot")
    apply(simp add: next_not_child_termination)
   apply(atomize)
   apply(erule_tac x=a in allE)
   apply(simp)
   apply(erule impE)
    apply(intro allI impI)
    apply(erule_tac x=q in allE)
    apply(erule impE)
     apply(simp add: descendants_of_def cdt_parent_defs)
     apply(rule_tac b=a in trancl_into_trancl)
      apply(simp)
     apply(simp)
    apply(simp)
   apply(erule impE)
    apply(erule_tac x=a in allE)
    apply(erule impE)
     apply(fastforce simp: descendants_of_def cdt_parent_defs)
    apply(simp)
   apply(subst next_not_child.psimps)
    apply(simp add: next_not_child_termination)
   apply(simp)
  using f_d apply(simp)
  done

lemma next_not_child_NoneI:
  "\<lbrakk>\<forall>q. p \<in> descendants_of q m \<longrightarrow> next_sib q t m = None;
    next_sib p t m = None; finite_depth m\<rbrakk>
    \<Longrightarrow> next_not_child p t m = None"
  by(simp add: next_not_child_NoneI')

lemma next_not_childD':
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes f_d: "finite_depth m" shows
  "\<lbrakk>next_not_child p t m = Some n; finite_depth m; no_mloop m\<rbrakk>
    \<Longrightarrow> next_sib p t m = Some n \<or>
       (next_sib p t m = None \<and>
         (\<exists>q. next_sib q t m = Some n \<and> p \<in> descendants_of q m
          \<and> (\<forall>q'. q' \<in> descendants_of q m \<and> p \<in> descendants_of q' m
           \<longrightarrow> next_sib q' t m = None)))"
  apply(induct p rule: next_not_child_pinduct[where t=t and m=m])
   apply(simp)
   apply(case_tac "m slot")
    apply(simp)
    apply(rule disjCI)
    apply(simp)
    apply(erule disjE)
     apply(erule exE, drule next_sibD)
     apply(simp add: next_sib_def)
    apply(simp add: next_not_child_termination split: if_split_asm)
   apply(atomize)
   apply(erule_tac x=a in allE)
   apply(simp)
   apply(case_tac "next_sib slot t m")
    apply(simp)
    apply(case_tac "next_not_child a t m = Some n")
     apply(simp)
     apply(erule disjE)
      apply(rule_tac x=a in exI)
      apply(simp)
      apply(rule conjI)
       apply(fastforce simp: descendants_of_def cdt_parent_defs)
      apply(intro impI allI)
      apply(simp add: descendants_of_def cdt_parent_defs)
      apply(erule conjE)
      apply(drule_tac x=q' in tranclD2)
      apply(elim exE conjE)
      apply(simp)
      apply(drule_tac b=q' and c=z in trancl_rtrancl_trancl)
       apply(simp)
      apply(simp add: no_mloop_def cdt_parent_defs)
     apply(elim conjE exE)
     apply(rule_tac x=q in exI)
     apply(simp)
     apply(rule conjI)
      apply(simp add: descendants_of_def cdt_parent_defs)
      apply(rule_tac b=a in trancl_into_trancl)
       apply(simp)
      apply(simp)
     apply(intro allI impI)
     apply(case_tac "a=q'")
      apply(simp)
     apply(erule_tac x=q' in allE)
     apply(erule impE)
      apply(simp add: descendants_of_def cdt_parent_defs)
      apply(erule conjE)
      apply(drule_tac y=slot in tranclD2)
      apply(elim conjE exE)
      apply(simp)
      apply(drule rtranclD)
      apply(simp)
     apply(simp)
    apply(simp add: next_not_child_termination)
   apply(simp add: next_not_child_termination)
  using f_d apply(simp)
  done

lemma next_not_childD:
   notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>next_not_child p t m = Some n; finite_depth m; no_mloop m\<rbrakk>
    \<Longrightarrow> next_sib p t m = Some n \<or>
       (next_sib p t m = None \<and>
         (\<exists>q. next_sib q t m = Some n \<and> p \<in> descendants_of q m
          \<and> (\<forall>q'. q' \<in> descendants_of q m \<and> p \<in> descendants_of q' m
           \<longrightarrow> next_sib q' t m = None)))"
  by (simp add: next_not_childD')

lemma next_not_child_NoneD':
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes f_d: "finite_depth m" shows
  "\<lbrakk>next_not_child p t m = None; finite_depth m\<rbrakk>
    \<Longrightarrow> (\<forall>q. p \<in> descendants_of q m \<longrightarrow> next_sib q t m = None) \<and>
        next_sib p t m = None"
  apply(induct p rule: next_not_child_pinduct[where t=t and m=m])
   apply(subgoal_tac "next_sib slot t m = None")
    prefer 2
    apply(subst(asm)(2) next_not_child.psimps)
     apply(simp add: next_not_child_termination)
    apply(case_tac "next_sib slot t m")
     apply(simp)
    apply(simp)
   apply(simp)
   apply(intro allI impI)
   apply(case_tac "m slot")
    apply(subst(asm)(2) next_not_child.psimps)
     apply(simp add: next_not_child_termination)
    apply(case_tac "next_sib slot t m")
     apply(simp add: descendants_of_def cdt_parent_defs)
     apply(drule tranclD2)
     apply(fastforce)
    apply(simp)
   apply(atomize)
   apply(erule_tac x=a in allE)
   apply(simp)
   apply(erule impE)
    apply(simp add: next_not_child_termination)
   apply(case_tac "q=a")
    apply(simp add: next_not_child_termination split: if_split_asm)
   apply(erule conjE)
   apply(erule_tac x=q in allE)
   apply(erule impE)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(drule tranclD2)
    apply(elim conjE exE)
    apply(simp)
    apply(drule rtranclD)
    apply(simp)
   apply(simp)
  using f_d apply(simp)
  done

lemma next_not_child_NoneD:
  "\<lbrakk>next_not_child p t m = None; finite_depth m\<rbrakk>
    \<Longrightarrow> (\<forall>q. p \<in> descendants_of q m \<longrightarrow> next_sib q t m = None) \<and>
        next_sib p t m = None"
  by (simp add: next_not_child_NoneD')

lemma slot_in_one_list:
  "\<lbrakk>c \<in> set (t p); c \<in> set (t p'); valid_list_2 t m\<rbrakk> \<Longrightarrow> p = p'"
  by (simp only: valid_list_2_def, simp)


lemma next_sib_inj:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>next_sib a t m = Some y; next_sib b t m = Some y; valid_list_2 t m\<rbrakk>
    \<Longrightarrow> a = b"
  apply(drule next_sibD)+
  apply(simp add: valid_list_2_def)
  apply(elim exE conjE)
  apply(frule_tac a=a in after_in_list_in_list)
  apply(frule_tac a=b in after_in_list_in_list)
  apply(rule_tac list="t pa" and x=y in after_in_list_inj)
    apply(simp)
   apply(simp)
  apply(simp)
  done

lemma no_mloop_descendants:
  "no_mloop m = (\<forall>x. x \<notin> descendants_of x m)"
  by (clarsimp simp: no_mloop_def descendants_of_def)

lemma no_mloop_descendants':
  "no_mloop m \<Longrightarrow> x \<notin> descendants_of x m"
  by (simp add: no_mloop_descendants del: split_paired_All)

lemma valid_list_2D:
  notes split_paired_All[simp del]
  shows
  "valid_list_2 t m \<Longrightarrow> src \<in> set (t p) \<Longrightarrow> m src = Some p"
  apply (simp add: valid_list_2_def)
  done


lemma replace_parent_ignore:
  notes split_paired_All[simp del]
  shows
  "valid_list_2 t m \<Longrightarrow> m src \<noteq> Some src_p \<Longrightarrow> (list_replace (t src_p) src dest) = (t src_p)"
  apply (rule list_replace_ignore)
  apply (clarsimp simp add: valid_list_2_def)
  done

lemma after_in_list_not_parent:
  notes split_paired_All[simp del]
  shows
  "valid_list_2 t m \<Longrightarrow> no_mloop m \<Longrightarrow> after_in_list (t x) z \<noteq> Some x"
  apply (rule notI)
  apply (frule(1) valid_list_2D[OF _ after_in_list_in_list])
  apply (frule(1) no_mloop_neq,simp)
  done

lemma ancestor_not_descendant:
notes split_paired_All[simp del]
shows
"no_mloop m \<Longrightarrow> src \<in> descendants_of src_p m \<Longrightarrow> src_p \<notin> descendants_of src m"
  apply (rule notI)
  apply (frule(1) descendants_trans)
   apply (simp add: no_mloop_def descendants_of_def)
  done

lemma child_descendant:
"m src = Some src_p \<Longrightarrow> src \<in> descendants_of src_p m"
  apply (simp add: descendants_of_def cdt_parent_rel_def is_cdt_parent_def)
  apply (rule r_into_trancl')
  apply simp
  done

lemmas parent_not_descendant = ancestor_not_descendant[OF _ child_descendant]

lemma next_sib_not_self:
notes split_paired_All[simp del]
shows
"valid_list_2 t m \<Longrightarrow> next_sib src t m \<noteq> Some src"
  apply (rule notI)
  apply (simp add: next_sib_def split: option.splits)
  apply (subgoal_tac "distinct (t (the (m src)))")
   apply (frule distinct_after_in_list_not_self[where src=src])
   apply simp
  apply (simp add: valid_list_2_def)
  done

lemma next_sib_same_parent:
notes split_paired_All[simp del] split_paired_Ex[simp del]
shows
"valid_list_2 t m \<Longrightarrow> next_sib sib t m = Some me \<Longrightarrow> \<exists>p. m sib = Some p \<and> m me = Some p"
  apply (simp add: next_sib_def split: option.splits)
  apply (drule after_in_list_in_list)
  apply (simp add: valid_list_2_def)
  done

lemma next_not_child_not_self:
notes split_paired_All[simp del] split_paired_Ex[simp del]
shows
"valid_list_2 t m \<Longrightarrow> finite_depth m \<Longrightarrow> no_mloop m \<Longrightarrow> next_not_child src t m \<noteq> Some src"
  apply (rule notI)
  apply (drule next_not_childD,simp+)
  apply (elim disjE)
   apply (frule next_sib_not_self[where src=src],simp)
  apply (elim conjE exE)
  apply (frule_tac me=src and sib=q in next_sib_same_parent,assumption)
  apply (elim exE conjE)
  apply (subgoal_tac "src \<notin> descendants_of q m")
   apply simp
  apply (rule sib_not_desc,simp+)
  done

lemma empty_list_empty_desc:
  "valid_list_2 t m \<Longrightarrow> (t p = []) = (descendants_of p m = {})"
  apply(drule_tac slot=p in next_child_None_empty_desc)
  apply(simp add: next_child_def)
  apply(case_tac "t p", simp+)
  done


lemma after_in_list_not_self_helper:
  "\<lbrakk>distinct list;
        after_in_list list c = Some c;
        (list, c) = (x # y # xs, a)\<rbrakk>
       \<Longrightarrow> False"
  apply (induct list arbitrary: x y xs a,simp)
  apply atomize
  apply (case_tac xs)
  apply (case_tac "aa =x")
   apply (case_tac "x = y",simp,simp)
   apply (simp split: if_split_asm)+
   done

lemma after_in_list_not_self:
  "\<lbrakk>m c = Some p; valid_list_2 t m\<rbrakk> \<Longrightarrow> after_in_list (t p) c \<noteq> Some c"
  apply (simp only: valid_list_2_def)
  apply (erule conjE)
  apply (drule_tac x = p in spec)+
  apply (thin_tac "set (t p) = {c. m c = Some p}")
  apply (rule notI)
  apply (rule_tac x = "(t p, c)" in after_in_list.cases, simp, simp)
  apply (blast intro: after_in_list_not_self_helper)
  done

lemma not_sib_self:
  "valid_list_2 t m \<Longrightarrow> next_sib slot t m \<noteq> Some slot"
  by (case_tac "m slot", auto simp: next_sib_def after_in_list_not_self)


lemma next_not_child_eq_next_sib_None:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next_not_child p t m = next_not_child q t m; p \<in> descendants_of a m \<or> p = a;
           a \<in> descendants_of q m; valid_list_2 t m; finite_depth m; no_mloop m\<rbrakk>
    \<Longrightarrow> next_sib a t m = None"
  apply(case_tac "next_not_child p t m")
   apply(drule(1) next_not_child_NoneD)
   apply(fastforce)
  apply(case_tac "next_not_child q t m")
   apply(simp)
  apply(subgoal_tac "aa=aaa")
   prefer 2
   apply(simp)
  apply(drule(2) next_not_childD)+
  apply(erule_tac P="next_sib p t m = Some aa" in disjE)
   apply(erule_tac P="next_sib q t m = Some aaa" in disjE)
    apply(simp)
    apply(drule(2) next_sib_inj)
    apply(simp)
    apply(erule disjE)
     apply(drule_tac a=q and c=q in descendants_trans)
      apply(simp)
     apply(simp add: no_mloop_descendants)
    apply(simp add: no_mloop_descendants)
   apply(elim exE conjE)
   apply(drule_tac a=p and b=qa in next_sib_inj)
     apply(simp)
    apply(simp)
   apply(simp)
   apply(erule disjE)
    apply(drule_tac a=qa and c=q in descendants_trans, simp)
    apply(drule_tac a=qa and c=qa in descendants_trans, simp)
    apply(simp add: no_mloop_descendants)
   apply(simp)
   apply(drule_tac a=a and c=a in descendants_trans, simp)
   apply(simp add: no_mloop_descendants)
  apply(erule_tac P="next_sib q t m = Some aaa" in disjE)
   apply(elim exE conjE, simp)
   apply(drule(2) next_sib_inj, fastforce)
  apply(elim exE conjE, simp)
  apply(drule(2) next_sib_inj, simp)
  apply(erule_tac x=a in allE)+
  apply(erule disjE)
   apply(simp)
   apply(erule impE)
    apply(rule_tac b=q in descendants_trans, simp+)
    done

lemma remove_collect: "{y. P y} - {x} = {y. P y \<and> y \<noteq> x}"
  apply blast
  done


locale mdb_insert_abs_simple =
fixes m :: cdt
fixes t :: cdt_list
fixes dest :: cslot_ptr
assumes valid_list : "valid_list_2 t m"


locale mdb_insert_abs_simple_parent = mdb_insert_abs_simple +
fixes dest_p :: cslot_ptr
fixes t' :: cdt_list

defines "t' \<equiv> t(dest_p := list_remove (t dest_p) dest)"

assumes dest: "m dest = Some dest_p"
begin

lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
    "
   valid_list_2 (t'(src := dest # (t' src)))
        (m(dest \<mapsto> src))"
  apply (insert valid_list dest)
  apply (simp add: valid_list_2_def t'_def)
  apply (simp add: list_remove_removed insert_Collect remove_collect)
  apply (intro impI conjI allI)
  apply (fastforce simp: list_remove_distinct cong: Collect_cong)+
  done

  lemma valid_list_post':
  "\<lbrakk> t' src = []\<rbrakk> \<Longrightarrow>
      valid_list_2 (t'(src := [dest]))
        (m(dest \<mapsto> src))"

  by (insert valid_list_post[where src=src],simp)


end

locale mdb_insert_abs_simple_no_parent = mdb_insert_abs_simple +
assumes dest: "m dest = None"

context mdb_insert_abs_simple_no_parent
begin

lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
   "valid_list_2 (t(src := dest # (t src)))
        (m(dest \<mapsto> src))"
  apply (insert valid_list dest)
  apply (fastforce simp: valid_list_2_def)
  done


lemma valid_list_post':
  "\<lbrakk> t src = []\<rbrakk> \<Longrightarrow>
      valid_list_2 (t(src := [dest]))
        (m(dest \<mapsto> src))"
  by (insert valid_list_post[where src=src],simp)
end

locale mdb_insert_abs_sib_simple_no_parent = mdb_insert_abs_simple_no_parent +

fixes src :: cslot_ptr
fixes n
defines "n \<equiv> m(dest := m src)"
assumes neq: "dest \<noteq> src"
begin

lemma valid_list_post_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>m src = None\<rbrakk> \<Longrightarrow> valid_list_2 t n"
  apply (insert valid_list dest)
  apply (simp add: valid_list_2_def n_def)
  done


lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>m src = Some p\<rbrakk>
    \<Longrightarrow> valid_list_2 (t(p := list_insert_after (t p) src dest)) n"
  apply (insert valid_list dest neq)
  apply (simp add: valid_list_2_def n_def)
  apply (fastforce simp: distinct_list_insert_after  set_list_insert_after)
  done

end


locale mdb_insert_abs_sib_simple_parent = mdb_insert_abs_simple_parent +

fixes src :: cslot_ptr
fixes n
defines "n \<equiv> m(dest := m src)"
assumes neq: "dest \<noteq> src"

context mdb_insert_abs_sib_simple_parent
begin

lemma valid_list_post_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>m src = None\<rbrakk> \<Longrightarrow> valid_list_2 t' n"
  apply (insert valid_list dest)
  apply (simp add: valid_list_2_def t'_def n_def)
  apply (simp add: list_remove_removed insert_Collect remove_collect)
  apply (fastforce simp: list_remove_distinct cong: Collect_cong)
  done


lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>m src = Some p\<rbrakk>
    \<Longrightarrow> valid_list_2 (t'(p := list_insert_after (t' p) src dest)) n"
  apply (insert valid_list dest neq)
  apply (simp add: valid_list_2_def t'_def n_def)
  apply (fastforce simp: distinct_list_insert_after list_remove_distinct set_list_insert_after list_remove_removed)
  done

end


context mdb_insert_abs
begin

lemma finite_depth_insert_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "finite_depth m \<Longrightarrow> finite_depth (m(dest \<mapsto> src))"
  apply(simp add: finite_depth_def descendants_child split del: if_split)
  apply(rule allI)
  apply(case_tac "slot=dest")
   apply(case_tac "m src")
    apply(rule_tac x=src in exI)
    apply(simp add: neq)
   apply(erule_tac x=src in allE)
   apply(elim exE conjE)
   apply(rule_tac x=p in exI)
   apply(simp)
   apply(rule notI)
   apply(simp add: desc neq)
  apply(erule_tac x=slot in allE)
  apply(elim conjE exE)
  apply(rule_tac x=p in exI)
  apply(simp add: neq)
  apply(intro conjI impI notI)
   apply(simp add: desc)
  apply(simp add: desc)
  done

lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "valid_list_2 t m
    \<Longrightarrow> valid_list_2 (t(src := dest # t src))
        (m(dest \<mapsto> src))"
  apply (insert dest)
  apply(fastforce simp: valid_list_2_def)
  done

lemma valid_list_post':
  "\<lbrakk>valid_list_2 t m; t src = []\<rbrakk>
    \<Longrightarrow> valid_list_2 (t(src := [dest]))
        (m(dest \<mapsto> src))"
  by (drule valid_list_post, simp)

lemma next_child:
  "next_child p (t(src := dest # t src))
     = (if p = src then Some dest else next_child p t)"
  apply(fastforce simp: next_child_def)
  done

lemma next_child':
  "t src = []
    \<Longrightarrow> next_child p (t(src := [dest])) = (if p = src then Some dest else next_child p t)"
  by (fastforce simp: next_child_def)

lemma next_sib:
  "valid_list_2 t m
    \<Longrightarrow> next_sib p (t(src := dest # t src))
        (m(dest \<mapsto> src))
     = (if p = dest then next_child src t else next_sib p t m)"
  apply(case_tac "next_child src t")
   apply(simp)
   apply(drule next_child_NoneD)
   apply(safe)[1]
    apply(rule_tac p=src in next_sib_NoneI)
    apply(simp)
   apply(case_tac "next_sib p t m")
    apply(simp)
    apply(drule next_sib_NoneD)
    apply(erule disjE)
     apply(rule next_sib_NoneI)
     apply(simp)
    apply(elim exE conjE)
    apply(rule_tac p=pa in next_sib_NoneI)
    apply(simp)
   apply(simp)
   apply(drule next_sibD)
   apply(elim exE conjE)
   apply(rule_tac p=pa in next_sibI)
    apply(simp)
   apply(fastforce simp: valid_list_2_def)
  apply(drule (1) next_childD)
  apply(simp, safe)
   apply(case_tac "next_child src t")
    apply(fastforce dest: next_child_NoneD)
   apply(simp)
   apply(fastforce dest: next_childD intro: next_sibI)
  apply(case_tac "next_sib p t m")
   apply(fastforce dest: next_sib_NoneD next_sibD intro: next_sib_NoneI next_sibI)+
   done

lemma next_sib':
  "\<lbrakk>valid_list_2 t m; t src = []\<rbrakk>
    \<Longrightarrow> next_sib p (t(src := [dest]))
        (m(dest \<mapsto> src))
     = (if p = dest then None else next_sib p t m)"
  by (fastforce dest: next_sib[where p=p] intro: next_child_NoneI)

lemma next_not_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m\<rbrakk>
  \<Longrightarrow> next_not_child p (t(src := dest # t src)) (m(dest \<mapsto> src))
          = (if p = dest then next_slot src t m
            else next_not_child p t m)"
  apply(simp)
  apply(intro conjI impI)
   apply(case_tac "next_slot src t m")
    apply(simp add: next_slot_def split: if_split_asm)
     apply(case_tac "t src", simp, simp add: next_child_def)
    apply(drule(1) next_not_child_NoneD)
    apply(rule next_not_child_NoneI)
      apply(simp add: next_sib' descendants_child no_mloop_descendants desc)
      apply(simp add: descendants_of_def)
     apply(simp add: next_sib')
    apply(simp add: finite_depth_insert_child)
   apply(simp add: next_slot_def split: if_split_asm)
    apply(rule next_not_childI)
     apply(simp add: next_sib)
    apply(simp add: finite_depth_insert_child)
   apply(drule(2) next_not_childD)
   apply(rule next_not_childI)
    apply(simp add: next_sib' descendants_child)
    apply(erule disjE)
     apply(rule_tac x=src in exI)
     apply(simp add: no_mloop_descendants desc neq)
     apply(intro allI impI conjI)
      apply(drule_tac a=src and b=q' and c=src in descendants_trans, simp)
      apply(simp)
     apply(simp add: descendants_of_def)
    apply(elim exE conjE)
    apply(rule_tac x=q in exI)
    apply(simp)
    apply(intro conjI impI notI allI)
      apply(simp add: desc)
     apply(simp add: descendants_of_def)
    apply(simp)
   apply(simp add: finite_depth_insert_child)
  apply(case_tac "next_not_child p t m")
   apply(simp)
   apply(drule(1) next_not_child_NoneD)
   apply(rule next_not_child_NoneI)
     apply(simp add: next_sib descendants_child neq desc)
    apply(simp add: next_sib)
   apply(simp add: finite_depth_insert_child)
  apply(simp)
  apply(drule(2) next_not_childD)
  apply(rule next_not_childI)
   apply(simp add: next_sib descendants_child split del: if_split)
   apply(erule disjE, simp, simp split del: if_split)
   apply(elim exE conjE)
   apply(rule_tac x=q in exI)
   apply(simp add: desc neq)
   apply(intro conjI impI notI)
    apply(simp add: desc)
   apply(simp add: desc)
  apply(simp add: finite_depth_insert_child)
  done

lemma next_not_child':
  "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m; t src = []\<rbrakk>
    \<Longrightarrow> next_not_child p (t(src := [dest])) (m(dest \<mapsto> src))
          = (if p = dest then next_not_child src t m
            else next_not_child p t m)"
  apply(drule(2) next_not_child[where p=p])
  apply(simp add: next_slot_def)
  done

lemma next_slot:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m\<rbrakk>
    \<Longrightarrow> next_slot p (t(src := dest # t src)) (m(dest \<mapsto> src))
     = (if p = src then Some dest
        else if p = dest then next_slot src t m
        else next_slot p t m)"
  apply(simp add: next_slot_def next_not_child next_child next_not_child' next_child')
  apply(rule impI)
  apply(drule next_child_None_empty_desc[where slot=dest])
  apply(simp add: next_child_def)
  apply(case_tac "t dest", simp, simp add: desc)
  done
end




context mdb_insert_abs_sib
begin

lemma finite_depth:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "finite_depth m \<Longrightarrow> finite_depth n"
  apply(simp add: finite_depth_def descendants)
  apply(simp add: n_def)
  apply(rule allI)
  apply(case_tac "slot=dest")
   apply(erule_tac x=src in allE)
   apply(elim exE conjE)
   apply(erule disjE)
    apply(rule_tac x=p in exI)
    apply(simp)
    apply(rule impI, simp add: desc)
   apply(rule_tac x=dest in exI)
   apply(simp)
  apply(erule_tac x=slot in allE)
  apply(elim exE conjE)
  apply(rule_tac x=p in exI)
  apply(simp)
  apply(rule impI)
  apply(simp add: desc)
  done

lemma valid_list_post_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m src = None\<rbrakk> \<Longrightarrow> valid_list_2 t n"
  apply(insert dest)
  apply(fastforce simp: n_def valid_list_2_def)
  done

lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m src = Some p\<rbrakk>
    \<Longrightarrow> valid_list_2 (t(p := list_insert_after (t p) src dest)) n"
  apply(insert dest)
  apply(fastforce simp: n_def valid_list_2_def set_list_insert_after distinct_list_insert_after)
  done

lemma next_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m src = Some src_p\<rbrakk>
    \<Longrightarrow> next_child p (t(src_p := list_insert_after (t src_p) src dest)) = next_child p t"
  apply(simp add: next_child_def)
  apply(case_tac "list_insert_after (t src_p) src dest")
   apply(simp)
   apply(case_tac "t src_p")
    apply(simp)
   apply(simp split: if_split_asm)
  apply(simp)
  apply(case_tac "t src_p")
   apply(simp)
  apply(simp split: if_split_asm)
  done

lemma next_sib_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m src = None\<rbrakk>
    \<Longrightarrow> next_sib p t n
    = (if p = src \<and> m src \<noteq> None then Some dest
       else if p = dest then next_sib src t m
       else next_sib p t m)"
  apply(simp add: n_def next_sib_def)
  done

lemma next_sib:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m src = Some src_p\<rbrakk>
    \<Longrightarrow> next_sib p (t(src_p := list_insert_after (t src_p) src dest)) n
    = (if p = src \<and> m src \<noteq> None then Some dest
       else if p = dest then next_sib src t m
       else next_sib p t m)"
  apply(subgoal_tac "dest \<notin> set (t src_p) \<and> src \<in> set (t src_p)")
   prefer 2
   apply(simp add: valid_list_2_def)
  apply(simp add: next_sib_def n_def neq list_insert_after_after valid_list_2_def)
  apply(case_tac "m p")
   apply(simp)
  apply(simp add: list_insert_after_after)
  done

lemma next_not_child_no_parent:
    notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m; m src = None\<rbrakk>
    \<Longrightarrow> next_not_child p t n
    = (if p = src then (if m src = None then None else Some dest)
       else if p = dest then next_not_child src t m
       else if p \<in> descendants_of src m
         \<and> next_not_child p t m = next_not_child src t m then
           (if m src = None then None else Some dest)
       else next_not_child p t m)"
  apply(simp)
  apply(intro conjI impI)
       apply(simp add: descendants_of_def)
      apply(simp add: no_mloop_def descendants_of_def)
     apply(subgoal_tac "next_not_child src t m = None")
      prefer 2
      apply(rule next_not_child_NoneI)
        apply(fastforce dest: descendants_of_NoneD)
       apply(simp add: next_sib_def)
      apply(simp)
     apply(erule conjE, simp)
     apply(drule(1) next_not_child_NoneD[where p=p])
     apply(rule next_not_child_NoneI)
       apply(simp add: next_sib_no_parent descendants desc)
      apply(simp add: next_sib_no_parent)
     apply(simp add: finite_depth)
    apply(case_tac "next_not_child src t m")
     apply(simp)
     apply(drule(1) next_not_child_NoneD, rule next_not_child_NoneI)
       apply(simp add: descendants next_sib_no_parent)
       apply(simp add: descendants_of_def )
      apply(simp add: next_sib_no_parent)
     apply(simp add: finite_depth)
    apply(simp)
    apply(drule(2) next_not_childD, rule next_not_childI)
     apply(erule disjE)
      apply(simp add: next_sib_no_parent descendants)
     apply(rule disjI2)
     apply(simp add: next_sib_no_parent descendants)
     apply(elim exE conjE)
     apply(rule_tac x=q in exI)
     apply(simp)
     apply(intro allI conjI impI notI)
      apply(simp add: desc)
     apply(simp add: descendants_of_def)
    apply(simp add: finite_depth)
   apply(rule next_not_child_NoneI)
     apply(intro allI impI)
     apply(fastforce simp: descendants split: if_split_asm dest: descendants_of_NoneD)
    apply(simp add: next_sib_no_parent)
    apply(simp add: next_sib_def)
   apply(simp add: finite_depth)
  apply(case_tac "next_not_child p t m")
   apply(simp add: next_sib_no_parent descendants desc finite_depth
        | drule next_not_child_NoneD | rule next_not_child_NoneI)+
  apply(simp add: next_sib_no_parent descendants desc
       | drule next_not_childD | rule next_not_childI | erule disjE)+
   apply(elim exE conjE)
   apply(rule_tac x=q in exI)
   apply(case_tac "m dest")
    apply(fastforce simp: next_sib_def)
   apply(fastforce simp: next_sib_def dest)
  apply(simp add: finite_depth)
  done

lemma next_not_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m; m src = Some src_p\<rbrakk>
    \<Longrightarrow> next_not_child p (t(src_p := list_insert_after (t src_p) src dest)) n
    = (if p = src then (if m src = None then None else Some dest)
       else if p = dest then next_not_child src t m
       else if p \<in> descendants_of src m
         \<and> next_not_child p t m = next_not_child src t m then
           (if m src = None then None else Some dest)
       else next_not_child p t m)"
  apply(simp)
  apply(intro conjI impI)
       apply(simp add: descendants_of_def)
      apply(simp add: no_mloop_def descendants_of_def)
     apply(erule conjE)
     apply(rule next_not_childI)
      apply(rule disjI2)
      apply(rule conjI)
       apply(simp add: next_sib)
       apply(rule_tac p=p and q=src in next_not_child_eq_next_sib_None)
            apply(simp_all)[6]
      apply(rule_tac x=src in exI)
      apply(simp add: next_sib descendants no_mloop_descendants desc)
      apply(intro allI impI)
      apply(rule_tac p=p and q=src in next_not_child_eq_next_sib_None)
           apply(simp_all add: no_mloop_descendants)[6]
     apply(simp add: finite_depth)
    apply(case_tac "next_not_child src t m")
     apply(simp)
     apply(drule(1) next_not_child_NoneD, rule next_not_child_NoneI)
       apply(simp add: descendants next_sib)
       apply(simp add: descendants_of_def no_mloop_def)
      apply(simp add: next_sib)
     apply(simp add: finite_depth)
    apply(simp)
    apply(drule(2) next_not_childD, rule next_not_childI)
     apply(erule disjE)
      apply(simp add: next_sib descendants)
     apply(rule disjI2)
     apply(simp add: next_sib descendants no_mloop_descendants)
     apply(simp add: descendants_of_def)
     apply(elim exE conjE)
     apply(rule_tac x=q in exI)
     apply(simp)
     apply(intro conjI impI notI)
      apply(simp add: desc)
     apply(simp add: descendants_of_def)
    apply(simp add: finite_depth)
   apply(rule next_not_childI)
    apply(rule disjI1)
    apply(simp add: next_sib)
   apply(simp add: finite_depth)
  apply(case_tac "next_not_child p t m")
   apply(frule(1) next_not_child_NoneD)
   apply(simp add: next_sib descendants desc finite_depth
        | rule next_not_child_NoneI)+
     apply(intro impI notI)
     apply(simp)
     apply(case_tac "next_not_child src t m")
      apply(simp)
     apply(drule(2) next_not_childD)
     apply(erule disjE, simp)
     apply(elim exE conjE)
     apply(drule_tac a=p and c=q in descendants_trans, simp, simp)
    apply(simp add: next_sib)
   apply(simp add: finite_depth)
  apply(simp add: next_sib descendants desc no_mloop_descendants
       | drule next_not_childD | rule next_not_childI | erule disjE)+
   apply(elim exE conjE)
   apply(rule_tac x=q in exI)
   apply(simp)
   apply(intro conjI impI notI)
         apply(simp_all add: desc finite_depth)
   apply(erule notE)
   apply(rule next_not_childI[symmetric])
    apply(simp)
    apply(rule_tac x=q in exI)
     apply(fastforce simp: descendants_of_def cdt_parent_defs)
   apply(simp add: finite_depth)
  apply(erule notE)
  apply(rule next_not_childI[symmetric])
   apply(simp)
  apply(simp add: finite_depth)
  done

lemma next_slot_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m; m src = None\<rbrakk>
    \<Longrightarrow> next_slot p t n
    = next_slot p t m"
  apply(subgoal_tac "next_not_child dest t m = None")
   prefer 2
   apply((rule next_not_child_NoneI | intro allI impI
    | simp add: descendants_of_def next_sib_def finite_depth dest)+)[1]
  apply(subgoal_tac "next_not_child src t m = None")
   prefer 2
   apply((rule next_not_child_NoneI | intro allI impI |
         drule(1) descendants_of_NoneD | simp add: next_sib_def finite_depth)+)[1]
  apply(simp add: next_slot_def next_not_child_no_parent)
  done

lemma next_slot:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; finite_depth m; no_mloop m; m src = Some src_p; t src = []\<rbrakk>
    \<Longrightarrow> next_slot p (t(src_p := list_insert_after (t src_p) src dest)) n
    = (if p = src then Some dest
       else if p = dest then next_slot src t m
       else next_slot p t m)"
  apply(simp)
  apply(intro impI conjI)
    apply(simp add: next_slot_def next_child next_not_child empty_list_empty_desc desc)
    apply(rule impI, insert dest_no_parent_d, simp)[1]
   apply(simp add: next_slot_def next_child next_not_child)
   apply(rule impI, simp add: no_mloop_weaken)
  apply(simp add: next_slot_def next_child next_not_child)
  apply(intro conjI impI)
             apply(simp_all)
      apply(erule conjE, drule_tac a=src_p and c=src_p in descendants_trans,
            simp add: child_descendant, simp add: no_mloop_descendants)+
   apply(simp add: empty_list_empty_desc)
  apply(simp only: set_empty[symmetric])
  apply(simp add: set_list_insert_after)
  done
end

crunch exst[wp]: set_cap "(\<lambda>s. P (exst s))" (wp: crunch_wps simp: crunch_simps)

lemma set_cap_caps_of_state3:
  "\<lbrace>\<lambda>s. P (caps_of_state s (p \<mapsto> cap)) (cdt s)  (exst s) (is_original_cap s)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv s. P (caps_of_state s) (cdt s) (exst s) (is_original_cap s)\<rbrace>"
  apply (rule_tac Q="\<lambda>rv s. \<exists>m mr t. P (caps_of_state s) m t mr
                    \<and> (cdt s = m) \<and> (exst s = t) \<and> (is_original_cap s = mr)"
           in hoare_post_imp)
   apply simp
  apply (wp hoare_vcg_ex_lift)
  apply (rule_tac x="cdt s" in exI)
  apply (rule_tac x="is_original_cap s" in exI)
  apply (simp add: fun_upd_def)
  done


lemma exst_cdt_update[iff]:
  "exst (s\<lparr>cdt := a\<rparr>) = exst s"
  by simp

definition valid_mdb_weak where
"valid_mdb_weak s \<equiv> mdb_cte_at (swp (cte_wp_at ((\<noteq>) NullCap)) s) (cdt s) \<and> no_mloop (cdt s)"

lemma self_parent_eq: "m src = Some src \<Longrightarrow> m(dest \<mapsto> src) = m (dest := m src)"
  by simp

lemma ex1_False: "(\<And>x. \<not>P x) \<Longrightarrow> \<not> (\<exists>!x. P x)" by auto

lemma set_cap_match: "(\<And>s x. P s = P (s\<lparr>kheap := x\<rparr>)) \<Longrightarrow> \<lbrace>P\<rbrace> set_cap a b \<lbrace>\<lambda>_.P\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def get_object_def)
  apply wpsimp
  done

crunches cap_insert_ext, empty_slot_ext, cap_swap_ext, create_cap_ext
  for all_but_exst[wp]:  "all_but_exst P"
  and (empty_fail) empty_fail[wp]
  (ignore_del: cap_insert_ext empty_slot_ext cap_swap_ext create_cap_ext)

interpretation cap_insert_ext_extended: is_extended "cap_insert_ext a b c d e"
  by (unfold_locales; wp)

lemma cap_insert_valid_list [wp]:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrace>valid_list\<rbrace>
    cap_insert cap src dest
   \<lbrace>\<lambda>_ s. valid_list s\<rbrace>"
  apply (simp add: cap_insert_def)
  apply(simp add: set_untyped_cap_as_full_def update_cdt_def set_cdt_def update_cdt_list_def set_cdt_list_def bind_assoc cap_insert_ext_def)
  apply (rule hoare_pre)
   apply (wp | simp cong: option.case_cong if_cong del: fun_upd_apply split del: if_split)+
       apply(wp set_cap_caps_of_state3)[1]
      apply (case_tac "is_untyped_cap src_cap \<and>
         is_untyped_cap cap \<and>
         obj_ref_of src_cap = obj_ref_of cap \<and>
         cap_bits_untyped src_cap = cap_bits_untyped cap")

       apply (simp del: fun_upd_apply split del: if_split)
       apply (wp set_cap_caps_of_state3)
      apply (simp only:)
      apply (simp del: fun_upd_apply split del: if_split)
     apply (wp get_cap_wp)+
  apply(intro allI impI conjI)
  apply (case_tac "src = dest")
   apply (simp add: cte_wp_at_caps_of_state fun_upd_idem del: fun_upd_apply)
   apply (case_tac "cdt s dest")
    apply (simp del: fun_upd_apply split del: if_split  cong: option.case_cong)
   apply (simp add: del: fun_upd_apply split del: if_split  cong: option.case_cong)

   apply (fastforce simp add: valid_list_2_def list_remove_removed list_remove_distinct)
  apply (case_tac "cdt s dest")

   apply (subgoal_tac "mdb_insert_abs_simple_no_parent (cdt s) (cdt_list s) dest")
    prefer 2
    apply (rule mdb_insert_abs_simple_no_parent.intro[OF mdb_insert_abs_simple.intro])
    apply simp
    apply (rule mdb_insert_abs_simple_no_parent_axioms.intro)
    apply simp

   apply (subgoal_tac "mdb_insert_abs_sib_simple_no_parent (cdt s) (cdt_list s) dest src")
    prefer 2
    apply (rule mdb_insert_abs_sib_simple_no_parent.intro,assumption)
    apply (rule mdb_insert_abs_sib_simple_no_parent_axioms.intro,simp)
   apply(case_tac"should_be_parent_of capa (is_original_cap s src) cap (is_cap_revocable cap capa)")
    apply (case_tac "cdt s src")
     apply (simp del: fun_upd_apply)
     apply (rule mdb_insert_abs_simple_no_parent.valid_list_post,simp)
    apply (case_tac "a = src")
     apply (simp del: fun_upd_apply)
     apply (subst self_parent_eq,assumption)
     apply (rule mdb_insert_abs_sib_simple_no_parent.valid_list_post,simp,simp)
    apply (simp add: fun_upd_twist del: fun_upd_apply)
    apply (rule mdb_insert_abs_simple_no_parent.valid_list_post,simp)
   apply (case_tac "cdt s src")
    apply (frule(1) mdb_insert_abs_sib_simple_no_parent.valid_list_post_no_parent)
    apply (simp del: fun_upd_apply)
   apply (simp del: fun_upd_apply)
   apply (frule(1) mdb_insert_abs_sib_simple_no_parent.valid_list_post)
   apply (simp del: fun_upd_apply)

  apply (subgoal_tac "mdb_insert_abs_simple_parent (cdt s) (cdt_list s) dest a")
   prefer 2
   apply (rule mdb_insert_abs_simple_parent.intro[OF mdb_insert_abs_simple.intro])
    apply simp
   apply (rule mdb_insert_abs_simple_parent_axioms.intro)
   apply simp
  apply (subgoal_tac "mdb_insert_abs_sib_simple_parent (cdt s) (cdt_list s) dest a src")
   prefer 2
   apply (rule mdb_insert_abs_sib_simple_parent.intro,assumption)
   apply (rule mdb_insert_abs_sib_simple_parent_axioms.intro,simp)
  apply(case_tac"should_be_parent_of capa (is_original_cap s src) cap (is_cap_revocable cap capa)")
   apply (case_tac "cdt s src")
    apply (simp del: fun_upd_apply)
    apply (rule mdb_insert_abs_simple_parent.valid_list_post,simp)
   apply (case_tac "aa = src")
    apply (simp del: fun_upd_apply)
    apply (subst self_parent_eq,assumption)
    apply (rule mdb_insert_abs_sib_simple_parent.valid_list_post,simp,simp)
   apply (simp add: fun_upd_twist del: fun_upd_apply)
   apply (rule mdb_insert_abs_simple_parent.valid_list_post,simp)
  apply (case_tac "cdt s src")
   apply (frule(1) mdb_insert_abs_sib_simple_parent.valid_list_post_no_parent)
   apply (simp del: fun_upd_apply)
  apply (simp del: fun_upd_apply)
  apply (frule(1) mdb_insert_abs_sib_simple_parent.valid_list_post)
  apply (simp del: fun_upd_apply)
  done

lemma cte_at_next_slot:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list s; valid_mdb s; finite_depth (cdt s)\<rbrakk>
    \<Longrightarrow> next_slot p (cdt_list s) (cdt s) = Some n \<Longrightarrow> cte_at p s"
  apply(simp add: next_slot_def)
  apply(simp split: if_split_asm)
   apply(drule next_childD, simp)
   apply(rule_tac p=n in descendants_of_cte_at2)
    apply(simp add: child_descendant)
   apply(simp)
  apply(subgoal_tac "next_not_child_dom (p, cdt_list s, cdt s)")
   prefer 2
   apply(simp add: next_not_child_termination valid_mdb_def valid_list_2_def)
  apply(simp split: if_split_asm)
   apply(case_tac "cdt s p")
    apply(simp)
   apply(rule descendants_of_cte_at)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(rule r_into_trancl, simp)
   apply(simp)
  apply(drule next_sibD)
  apply(elim exE conjE)
  apply(drule after_in_list_in_list)
  apply(rule descendants_of_cte_at)
   apply(simp add: descendants_of_def cdt_parent_defs)
   apply(rule r_into_trancl, simp)
  apply(simp)
  done

lemma cte_at_next_slot':
  "\<lbrakk>valid_list s; valid_mdb s; finite_depth (cdt s)\<rbrakk>
    \<Longrightarrow> next_slot p (cdt_list s) (cdt s) = Some n \<Longrightarrow> cte_at n s"
  apply(simp add: next_slot_def)
  apply(simp split: if_split_asm)
   apply(drule next_childD, simp)
   apply(rule_tac x=p in descendants_of_cte_at, simp add: child_descendant, simp)
  apply(rule next_not_child_pinduct2[where t="cdt_list s" and p=p
                                             and m="cdt s"])
      apply(rule_tac p=a in descendants_of_cte_at2)
       apply(fastforce simp: descendants_of_def cdt_parent_defs)
      apply(simp)
     apply(assumption)
    apply(simp add: next_not_child_termination valid_mdb_def valid_list_2_def
               split: if_split_asm)
     apply(case_tac "cdt s p")
      apply(simp)
     apply(simp)
     apply(rule descendants_of_cte_at)
      apply(fastforce simp: descendants_of_def cdt_parent_defs)
     apply(simp add: valid_mdb_def)
    apply(drule next_sibD)
    apply(case_tac "cdt s p")
     apply(simp)
    apply(rule descendants_of_cte_at)
     apply(fastforce simp: descendants_of_def cdt_parent_defs)
    apply(simp add: valid_mdb_def)
   apply(intro allI impI, drule next_sibD)
    apply(simp)
   apply(elim exE conjE)
   apply(drule_tac after_in_list_in_list)
   apply(simp add: valid_list_2_def)
   apply(rule_tac x="(aa, b)" in descendants_of_cte_at, simp add: child_descendant, simp)
  apply(simp)
  done

lemma Collect_union: "{c. P c} \<union> {c. Q c} = {c. P c \<or> Q c}"
  apply blast
  done

locale mdb_move_abs_simple =
fixes m m' m'' :: cdt
fixes t t' t''
fixes src dest
fixes valid_list_post
assumes neq : "src \<noteq> dest"
assumes valid_list: "valid_list_2 t m"
defines "t' \<equiv> case m dest of Some dest_p \<Rightarrow> t(dest_p := list_remove (t dest_p) dest) | None \<Rightarrow> t"
defines "t'' \<equiv> case m src of Some src_p \<Rightarrow> t'(src_p := list_replace (t' src_p) src dest) | None \<Rightarrow> t'"

defines "m'' \<equiv> \<lambda>r. if r = src then None else (m(dest := m src)) r"
defines "m' \<equiv>
     \<lambda>r. if m'' r = Some src then Some dest
         else (m(dest := m src, src := None)) r"
begin

lemma valid_list_post_no_parents:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes replace_distinct[simplified list_replace_def,simp]
  shows
  "m src = None \<Longrightarrow> m dest = None \<Longrightarrow> valid_list_2 (t''(src := [], dest := (t'' src) @ (t'' dest))) m'"
  apply (insert valid_list neq)
  apply (simp add: m'_def m''_def t'_def t''_def valid_list_2_def list_replace_def)
  apply (intro impI conjI allI)
  apply fastforce
  apply fastforce
  apply fastforce
  done

lemma valid_list_post_src_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes replace_distinct[simplified list_replace_def,simp]
  notes list_remove_distinct[simp]
  shows
  "m src = None \<Longrightarrow> m dest = Some dest_p \<Longrightarrow> valid_list_2 (t''(src := [], dest := (t'' src) @ (t'' dest))) m'"
  apply (insert valid_list neq)
  apply (simp add: m'_def m''_def t'_def t''_def valid_list_2_def list_replace_def list_remove_removed)
  apply (intro impI conjI allI)
  apply fastforce+
  done

lemma valid_list_post_dest_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes replace_distinct[simplified list_replace_def,simp]
  notes list_remove_distinct[simp]
  shows
  "m src = Some src_p \<Longrightarrow> m dest = None \<Longrightarrow> valid_list_2 (t''(src := [], dest := (t'' src) @ (t'' dest))) m'"
  apply (insert valid_list neq)
  apply (simp add: m'_def m''_def t'_def t''_def valid_list_2_def list_replace_def list_remove_removed)
  apply (intro impI conjI allI)
  apply fastforce+
  done

lemma valid_list_post_parents:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes replace_distinct[simplified list_replace_def,simp]
  notes list_remove_distinct[simp]
  shows
  "m src = Some src_p \<Longrightarrow> m dest = Some dest_p \<Longrightarrow> valid_list_2 (t''(src := [], dest := (t'' src) @ (t'' dest))) m'"
  apply (insert valid_list neq)
  apply (simp add: m'_def m''_def t'_def t''_def )
  apply (intro impI conjI allI)
  apply (simp_all add: valid_list_2_def)
  apply (simp_all add: list_replace_def list_remove_removed)
  apply (intro impI conjI allI | fastforce)+
  done


lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes replace_distinct[simplified list_replace_def,simp]
  shows "valid_list_2 (t''(src := [], dest := (t'' src) @ (t'' dest))) m'"
  apply (case_tac "m src")
  apply (case_tac "m dest")
  apply (simp add: valid_list_post_no_parents)
  apply (simp add: valid_list_post_src_no_parent)
  apply (case_tac "m dest")
  apply (simp add: valid_list_post_dest_no_parent)
  apply (simp add: valid_list_post_parents)
  done

end




locale mdb_move_abs' = mdb_move_abs + constrains s::"det_ext state"

context mdb_move_abs'
begin

lemma findepth : "finite_depth m"
  apply (simp add: m)
  apply (rule Deterministic_AI.finite_depth)
  apply (rule valid_mdb)
  done

lemma finite_depth:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "finite_depth m'"
  apply (insert findepth)
  apply(simp add: finite_depth_def descendants)
  apply(rule allI)
  apply(case_tac "slot=dest")
   apply(erule_tac x=src in allE)
   apply(elim exE conjE)
   apply(erule disjE)
    apply(rule_tac x=p in exI)
    apply(simp add: m'_def m''_def)
    apply(rule conjI)
     apply(rule impI, simp add: dest_desc)
    apply(intro impI notI)
    apply(insert valid_mdb)[1]
    apply(drule_tac slot=src in desc_not_parent, simp add: m)
   apply(simp add: m'_def m''_def)
   apply(fastforce)
  apply(simp add: m'_def m''_def)
  apply(erule_tac x=slot in allE)
  apply(elim exE conjE)
  apply(case_tac "p=src")
   apply(erule disjE)
    apply(rule_tac x=dest in exI)
    apply(simp)
   apply(rule_tac x=src in exI)
   apply(simp)
  apply(case_tac "slot=src")
   apply(rule_tac x=src in exI)
   apply(simp)
  apply(rule_tac x=p in exI)
  apply(simp)
  apply(intro conjI impI)
   apply(simp add: dest_desc)
  apply(simp add: dest_desc)
  done

lemma valid_list_post_helper:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>dest \<notin> set list;
     distinct list\<rbrakk>
    \<Longrightarrow> distinct
        (map (\<lambda>x. if x = src then dest else x) list)"
  apply (induct list)
  apply force+
  done


lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m src = Some src_p\<rbrakk>
    \<Longrightarrow> valid_list_2 (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src)) m'"
  apply (simp add: valid_list_2_def)
  apply (rule Collect_cong | simp add: list_replace_def m'_def m''_def split: if_split_asm | intro iffI impI conjI notI allI | force | fastforce)+
  apply clarsimp
  apply (subgoal_tac "dest \<notin> set (t src_p)")
   apply (blast intro: valid_list_post_helper)
  apply simp
  done

lemma valid_list_post_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m src = None\<rbrakk>\<Longrightarrow> valid_list_2 (t(src := [], dest := t src)) m'"
  apply(simp add: valid_list_2_def)
  apply (rule Collect_cong | simp add: list_replace_def m'_def m''_def split: if_split_asm | intro iffI impI conjI notI allI | fastforce)+
  done


lemma next_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "valid_list_2 t m \<Longrightarrow> m src = Some src_p
    \<Longrightarrow> next_child p (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src))
      = (if p = src then None
         else if p = dest then next_child src t
         else if next_child p t = Some src then Some dest
         else next_child p t)"
  apply (simp split: if_split)
  apply (clarsimp simp: next_child_def list_replace_def)
  apply (intro impI conjI)
    apply (fold next_child_def)[1]
    apply (frule(1) next_childD)
    apply clarsimp
   apply (case_tac "t src_p",simp+)
  apply (case_tac "t p",simp)
  apply (simp add: valid_list_2_def)
  apply (subgoal_tac "src \<in> set (t p)")
   apply (thin_tac "t p = src # list")
   apply simp+
  done


lemma next_child_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "valid_list_2 t m \<Longrightarrow> m src = None
    \<Longrightarrow> next_child p (t(src := [], dest := t src))
      = (if p = src then None
         else if p = dest then next_child src t
         else if next_child p t = Some src then Some dest
         else next_child p t)"
  apply (simp split: if_split)
  apply (clarsimp simp add: next_child_def)
  apply (fold next_child_def)
  apply (frule(1) next_childD,clarsimp)
  done

lemma next_sib_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "valid_list_2 t m \<Longrightarrow> m src = None
    \<Longrightarrow> next_sib p (t(src := [], dest := t src)) m'
      = (if p = src then None
         else if p = dest then next_sib src t m
         else if next_sib p t m = Some src then Some dest
         else next_sib p t m)"
  apply (simp add: next_sib_def m'_def m''_def split: if_split)
  apply (intro impI conjI)
    apply (simp split: option.splits  | drule(1) valid_list_2D[OF _ after_in_list_in_list])+
   done






lemma next_sib:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "valid_list_2 t m \<Longrightarrow> m src = Some src_p
    \<Longrightarrow> next_sib p (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src)) m'
      = (if p = src then None
         else if p = dest then next_sib src t m
         else if next_sib p t m = Some src then Some dest
         else next_sib p t m)"
  apply (simp add: next_sib_def m'_def m''_def split: if_split)
  apply (intro impI conjI)
    apply (intro impI | simp split: option.splits  | drule(1) valid_list_2D[OF _ after_in_list_in_list] | rule after_in_list_list_replace | rule replace_list_preserve_after replace_list_preserve_after' | simp add: valid_list_2_def)+
    done

lemma next_not_child_root:
  assumes findepth: "finite_depth k"
  shows
  "k p = None \<Longrightarrow> next_not_child p t k = None"
  apply (subst next_not_child.psimps[OF next_not_child_termination[OF findepth]])
  apply (simp add: next_sib_def)
  done



lemma next_not_child_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes nnext = next_not_child.psimps[OF next_not_child_termination[OF findepth]]
  notes nnext' = next_not_child.psimps[OF next_not_child_termination[OF finite_depth]]
  notes nnext'' = nnext'[simplified m'_def m''_def]
  shows
  "valid_list_2 t m \<Longrightarrow> m src = None
    \<Longrightarrow> next_not_child p (t(src := [], dest := t src)) m'
      = (if p = src then None
         else if p = dest then next_not_child src t m
         else if next_not_child p t m = Some src then Some dest
         else next_not_child p t m)"
  apply (induct p rule: next_not_child_pinduct[where t=t and m=m, OF _ findepth])
  apply (case_tac "m slot")
   apply (subst next_not_child_root[OF findepth],assumption)+
   apply (subst next_not_child_root[OF finite_depth])
    apply ((simp add: m'_def m''_def)+)[2]
  apply (case_tac "next_sib slot t m")
   apply (drule_tac x="a" in meta_spec)
   apply (simp add: m'_def m''_def next_sib_def nnext nnext'' cong: if_weak_cong split: if_split_asm)
  apply (simp split del: if_split)
  apply (thin_tac "\<And>a. \<lbrakk>False; Q a\<rbrakk> \<Longrightarrow> P a" for Q P)
  apply (simp add: m'_def m''_def next_sib_def nnext nnext'' cong: if_weak_cong split: if_split_asm | intro impI conjI)+
    apply (simp add: valid_list_2_def | drule after_in_list_in_list | clarsimp)+
    done

lemma m'_helper: "m src = k \<Longrightarrow> m' dest = k"
  apply (clarsimp simp: m'_def m''_def)+
  done

lemma m'_helper2: "x \<noteq> src \<Longrightarrow> x \<noteq> dest \<Longrightarrow> m x \<noteq> Some src \<Longrightarrow> m' x = m x"
  apply (clarsimp simp: m'_def m''_def)
  done

lemma m'_helper3: "x \<noteq> dest \<Longrightarrow> m x = Some src \<Longrightarrow> m' x = Some dest"
  apply (clarsimp simp: m'_def m''_def)
  done

lemma m'_helper4: "m' src = None"
  apply (clarsimp simp: m'_def m''_def)
  done

lemmas m'_helpers = m'_helper m'_helper2 m'_helper3 m'_helper4

lemma not_self[simp]: "m x \<noteq> Some x"
  apply clarsimp
  apply (insert no_mloop)
  apply (frule no_mloop_neq)
  apply simp+
  done

lemma src_loop_facts:  "m src = Some src_p \<Longrightarrow> m src_p \<noteq> Some src" "m src = Some src_p \<Longrightarrow> src_p \<noteq> src"
  apply -
  apply (rule notI)
   apply (frule child_descendant)
   apply (frule parent_not_descendant[OF no_mloop],simp)
  apply (rule notI)
  apply simp
  done




lemma next_not_child_parent:
notes split_paired_All[simp del] split_paired_Ex[simp del]
shows
"\<lbrakk>valid_list_2 t m; m src = Some src_p\<rbrakk>
    \<Longrightarrow> next_not_child src_p (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src)) m' =
       next_not_child src_p t m"
  apply (case_tac "src_p = dest",simp)
  apply (insert src_loop_facts[where src_p=src_p])
  apply (rule next_not_child_linearI'[OF findepth finite_depth])
    apply (simp add: m'_def m''_def)
   apply (simp add: next_sib)
   apply (rule notI)
   apply (frule(1) next_sib_same_parent,simp)
  apply (intro impI allI conjI)
   apply (simp add: m'_def m''_def)
   apply (intro impI conjI)
     apply (rule notI)
     apply simp
     apply (cut_tac dest_desc,simp)
    apply (rule notI)
    apply simp
    apply (frule parent_not_descendant[OF no_mloop],simp)
   apply (rule notI)
   apply (subgoal_tac "q \<in> descendants_of src_p m")
    apply (frule ancestor_not_descendant[OF no_mloop],simp)
   apply (rule descendants_trans)
    apply (rule child_descendant)
    apply simp
   apply (rule child_descendant)
   apply simp
  apply (simp add: next_sib)
  apply (intro impI conjI)
    apply (simp add:  m'_helpers)+
    apply (frule(1) next_sib_same_parent,simp)
    apply (frule parent_not_descendant[OF no_mloop],simp)
   apply (simp add: m'_def m''_def)+
  done



lemma next_not_child_helper':
notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes nnext = next_not_child.psimps[OF next_not_child_termination[OF findepth]]
  notes nnext' = next_not_child.psimps[OF next_not_child_termination[OF finite_depth]]
shows
"\<lbrakk>valid_list_2 t m; m src = Some src_p; m slot = None\<rbrakk>
           \<Longrightarrow> next_not_child slot (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src))
               m' =
              (if slot = src then None
               else if slot = dest then next_not_child src t m
                    else if next_not_child slot t m = Some src then Some dest
                         else next_not_child slot t m)"
  apply (simp add: next_sib m'_helpers
          nnext[where slot=slot]
          nnext[where slot=dest]
          nnext[where slot=src]
          nnext'[where slot=slot]
          nnext'[where slot=dest]
          nnext'[where slot=src])
  apply (intro impI conjI,simp_all)
  apply (rule next_not_child_parent,simp+)+
  done

lemma next_not_child_helper'':
notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes nnext = next_not_child.psimps[OF next_not_child_termination[OF findepth]]
  notes nnext' = next_not_child.psimps[OF next_not_child_termination[OF finite_depth]]

shows
  "\<lbrakk>valid_list_2 t m; m src = Some src_p; m slot = Some a;
        next_sib slot t m = Some aa\<rbrakk>
       \<Longrightarrow> next_not_child slot (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src)) m' =
          (if slot = src then None
           else if slot = dest then next_not_child src t m
                else if next_not_child slot t m = Some src then Some dest else next_not_child slot t m)"
  apply (simp add: next_sib m'_helpers
          nnext[where slot=slot]
          nnext'[where slot=slot] )
  apply (intro impI conjI,simp_all)
  done

lemma next_not_child_helper''':
notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes nnext = next_not_child.psimps[OF next_not_child_termination[OF findepth]]
  notes nnext' = next_not_child.psimps[OF next_not_child_termination[OF finite_depth]]

shows
"\<lbrakk>valid_list_2 t m; m src = Some src_p; src_p \<noteq> src; m src_p \<noteq> Some src; m slot = Some a;
        next_not_child a (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src)) m' =
        (if a = src then None
         else if a = dest then next_not_child src t m
              else if next_not_child a t m = Some src then Some dest else next_not_child a t m);
        next_sib slot t m = None\<rbrakk>
       \<Longrightarrow> next_not_child slot (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src)) m' =
          (if slot = src then None
           else if slot = dest then next_not_child src t m
                else if next_not_child slot t m = Some src then Some dest else next_not_child slot t m)"
  apply (case_tac "src_p = dest")
  apply simp
  apply (simp add: next_sib m'_helpers
          nnext[where slot=slot]
          nnext[where slot=dest]
          nnext[where slot=src]

          nnext'[where slot=slot]
          nnext'[where slot=dest]
          nnext'[where slot=src]
split: if_split_asm)
    apply (intro impI conjI,simp_all)
      apply (drule next_not_childD[OF _ findepth no_mloop])
      apply (elim disjE)
       apply (frule(1) next_sib_same_parent,simp)
      apply (elim conjE exE)
      apply (frule (1) next_sib_same_parent,simp)
      apply (frule parent_not_descendant[OF no_mloop],simp)
     apply (rule next_not_child_parent,simp+)
    apply (frule next_sib_not_self[where src=src],simp)
   apply (intro impI conjI)
    apply (rule next_not_child_parent,simp+)
  apply (intro impI conjI)
   apply (rule next_not_child_parent,simp+)
  done


lemma next_not_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes nnext = next_not_child.psimps[OF next_not_child_termination[OF findepth]]
  notes nnext' = next_not_child.psimps[OF next_not_child_termination[OF finite_depth]]
  assumes misc: "valid_list_2 t m" "m src = Some src_p"
  shows
  "next_not_child p (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src)) m'
      = (if p = src then None
         else if p = dest then next_not_child src t m
         else if next_not_child p t m = Some src then Some dest
         else next_not_child p t m)"
  apply (insert misc)
  apply (insert src_loop_facts[where src_p=src_p],simp split del: if_split)
  apply (induct p rule: next_not_child_pinduct[where t=t and m=m, OF _ findepth])
  apply (case_tac "m slot")
   apply (rule next_not_child_helper',(simp split del: if_split)+)
  apply (drule_tac x=a in meta_spec)
  apply (simp split del: if_split)
  apply (case_tac "next_sib slot t m")
   apply (rule next_not_child_helper''',(simp split del: if_split)+)
  apply (rule next_not_child_helper'',(simp split del: if_split)+)
  done


lemma next_slot_no_parent:
  "valid_list_2 t m \<Longrightarrow> m src = None
    \<Longrightarrow> next_slot p (t(src := [], dest := t src)) m'
      = (if p = src then None
         else if p = dest then next_slot src t m
         else if next_slot p t m = Some src then Some dest
         else next_slot p t m)"
  apply (simp only: next_slot_def split: if_split)
  apply (intro impI conjI)
  apply (subst next_child_no_parent| subst next_not_child_no_parent | simp)+
  done



lemma next_slot:
  "valid_list_2 t m \<Longrightarrow> m src = Some src_p
    \<Longrightarrow> next_slot p (t(src_p := list_replace (t src_p) src dest, src := [], dest := t src)) m'
      = (if p = src then None
         else if p = dest then next_slot src t m
         else if next_slot p t m = Some src then Some dest
         else next_slot p t m)"
  apply (simp only: next_slot_def split: if_split)
  apply (intro impI conjI)
  apply (subst next_child | subst next_not_child | (simp split: if_split_asm) | intro impI conjI)+
  done

end

lemma
notes split_paired_All[simp del]
shows
"\<lbrakk>valid_list_2 t m\<rbrakk>
        \<Longrightarrow> valid_list_2
            (case m dest of None \<Rightarrow> t
             | Some a \<Rightarrow> t
                 (a := list_remove (t a) dest))
            (m(dest := None))"

  apply (case_tac "m dest")
  apply (fastforce simp: valid_list_2_def list_remove_removed intro: list_remove_distinct)+
  done

lemma cap_move_valid_list [wp]:

  notes split_paired_All[simp del]
  shows
  "\<lbrace>valid_list\<rbrace>
  cap_move cap src dest
  \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (case_tac "src = dest")
   apply (simp add: cap_move_def)
   apply(simp add: set_cdt_def cap_move_ext_def
                    update_cdt_list_def set_cdt_list_def del: fun_upd_apply split del: if_split)
   apply(wp)
    apply (simp del: fun_upd_apply cong: option.case_cong)
    apply (wp set_cap_caps_of_state3)+
   apply (case_tac "cdt s dest")
    apply (fastforce simp: valid_list_2_def list_remove_removed intro: list_remove_distinct)+
  apply (simp add: cap_move_def)
  apply(simp add: cap_move_def set_cdt_def cap_move_ext_def bind_assoc
                  update_cdt_list_def set_cdt_list_def del: fun_upd_apply split del: if_split)
  apply(wp)
   apply (simp del: fun_upd_apply split del: if_split)
   apply (unfold valid_list_2_def)
   apply (simp del: fun_upd_apply cong: option.case_cong split del: if_split)
   apply (wp set_cap_caps_of_state3)+
  apply (fold valid_list_2_def)
  apply (rule mdb_move_abs_simple.valid_list_post)
  apply (rule mdb_move_abs_simple.intro; simp)
  done


lemma next_sib_share_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next_sib a t m = Some b; valid_list_2 t m\<rbrakk>
    \<Longrightarrow> a \<in> descendants_of c m = (b \<in> descendants_of c m)"
  apply(drule next_sibD)
  apply(case_tac "m a", simp, simp)
  apply(subgoal_tac "m b = Some aa")
   prefer 2
   apply(fastforce simp: after_in_list_in_list valid_list_2_def)
  apply(simp add: descendants_of_def cdt_parent_defs)
  apply(case_tac "c=aa")
   apply(fastforce)
  apply(rule iffI)
   apply(rule_tac b=aa in trancl_into_trancl)
    apply(drule tranclD2)
    apply(simp)
    apply(drule rtranclD)
    apply(simp)
   apply(simp)
  apply(rule_tac b=aa in trancl_into_trancl)
   apply(drule tranclD2)
   apply(simp)
   apply(drule rtranclD)
   apply(simp)
  apply(simp)
  done

lemma desc_sib_ne:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>a \<in> descendants_of b m; next_sib b t m = Some c; valid_list_2 t m;
    no_mloop m\<rbrakk>
    \<Longrightarrow> a \<noteq> c"
  apply(rule notI)
  apply(drule next_sibD)
  apply(case_tac "m b", simp, simp)
  apply(subgoal_tac "aa \<in> descendants_of aa m")
   prefer 2
   apply(simp add: descendants_of_def cdt_parent_defs)
   apply(rule_tac b=b in trancl_into_trancl2)
    apply(simp)
   apply(drule tranclD2)
   apply(simp)
   apply(drule after_in_list_in_list)
   apply(simp add: valid_list_2_def)
   apply(drule rtranclD)
   apply(fastforce)
  apply(simp add: no_mloop_descendants)
  done

lemma (in mdb_empty_abs) finite_depth:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "finite_depth m \<Longrightarrow> finite_depth n"
  apply(simp add: finite_depth_def descendants)
  apply(rule allI)
  apply(simp add: n_def)
  apply(case_tac "slota=slot")
   apply(simp)
  apply(simp)
  apply(erule_tac x=slota in allE)
  apply(elim exE conjE)
  apply(case_tac "p=slot")
   apply(simp)
   apply(subgoal_tac "\<exists>a. m a = Some slot \<and>
               (slota \<in> descendants_of a m \<or> slota = a)")
    prefer 2
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(drule tranclD)
    apply(elim exE conjE)
    apply(simp)
    apply(rule_tac x=z in exI)
    apply(simp)
    apply(drule rtranclD)
    apply(erule disjE)
     apply(simp)
    apply(simp)
   apply(erule exE)
   apply(rule_tac x=a in exI)
   apply(simp)
   apply(fastforce)
  apply(rule_tac x=p in exI)
  apply(simp)
  done



lemma distinct_list_replace_list:
 "\<lbrakk>distinct list; distinct list'; set list \<inter> set list' = {}; slot \<in> set list\<rbrakk>
    \<Longrightarrow> distinct (list_replace_list list slot list')"
  apply(induct list)
   apply(simp)
  apply(simp)
  apply(intro conjI impI)
    apply(fastforce)
   apply(subst set_list_replace_list)
      apply(simp)
     apply(simp)
    apply(fastforce)
   apply(simp)
  apply(simp)
  done


locale mdb_empty_abs_simple =
fixes m n t slot
assumes valid_list: "valid_list_2 t m"
defines "n \<equiv> (\<lambda>p. if m p = Some slot then m slot else m p)(slot := None)"
begin

lemma valid_list_post_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>m slot = None\<rbrakk> \<Longrightarrow> valid_list_2 (t(slot := [])) n"
  apply (insert valid_list)
  apply(simp add: valid_list_2_def n_def)
  apply(intro conjI impI allI notI)
  apply(fastforce)
  done

lemma valid_list_post_self_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>m slot = Some slot_p; slot_p = slot\<rbrakk>
    \<Longrightarrow> valid_list_2 (t(slot_p := list_remove (t slot_p) slot)) n"
  apply (insert valid_list)
  apply (simp add: valid_list_2_def n_def list_remove_removed list_remove_distinct)
  apply fastforce
  done

lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>m slot = Some slot_p; slot_p \<noteq> slot\<rbrakk>
    \<Longrightarrow> valid_list_2 (t(slot_p := list_replace_list (t slot_p) slot (t slot), slot := [])) n"
  apply (insert valid_list)
  apply(simp add: valid_list_2_def n_def)
  apply(intro conjI impI allI)
  apply (fastforce simp: set_list_replace_list intro!: distinct_list_replace_list)+
  done
end

locale mdb_empty_abs' = mdb_empty_abs + constrains s::"det_ext state"



lemma (in mdb_empty_abs') valid_list_post_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = None\<rbrakk> \<Longrightarrow> valid_list_2 (t(slot := [])) n"
  apply(simp add: valid_list_2_def)
  apply(intro conjI impI allI notI)
   apply(simp add: n_def split: if_split_asm)
  apply(fastforce simp: n_def split: if_split_asm)
  done



lemma (in mdb_empty_abs') valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = Some slot_p\<rbrakk>
    \<Longrightarrow> valid_list_2 (t(slot_p := list_replace_list (t slot_p) slot (t slot), slot := [])) n"
  apply(simp add: valid_list_2_def)
  apply(intro conjI impI allI)
      apply(simp)
     apply(simp add: n_def)
     apply(fastforce simp: set_list_replace_list n_def)
    apply(simp add: n_def)
   apply(simp add: n_def, fastforce)
  apply(rule distinct_list_replace_list)
     apply(simp)+
   apply(rule ccontr)
   apply(fastforce dest: int_not_emptyD)
  apply(simp)
  done

lemma (in mdb_empty_abs') next_child_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = None\<rbrakk>
    \<Longrightarrow> next_child p (t(slot := []))
    = (if p = slot then None
      else next_child p t)"
  apply(simp, intro conjI impI)
   apply(rule next_child_NoneI)
   apply(simp)
  apply(case_tac "next_child p t")
   apply(simp)
   apply(rule next_child_NoneI, drule next_child_NoneD)
   apply(simp)
  apply(simp)
  apply(drule(1) next_childD)
  apply(elim exE conjE)
  apply(rule next_childI)
  apply(simp)
  done

lemma (in mdb_empty_abs') next_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = Some slot_p\<rbrakk>
    \<Longrightarrow> next_child p (t(slot_p := list_replace_list (t slot_p) slot (t slot), slot := []))
     = (if p = slot then None
       else if next_child p t = Some slot then
         if t slot = [] then
           if t p = [slot] then None
           else if hd (t p) = slot then after_in_list (t p) slot
           else Some (hd (t p))
         else next_child slot t
       else next_child p t)"
  apply(case_tac "p=slot")
   apply(fastforce intro: next_child_NoneI dest: next_child_NoneD)
  apply(case_tac "next_child p t = Some slot")
   apply(simp split del: if_split)
   apply(drule(1) next_childD)
   apply(elim exE conjE)
   apply(case_tac "t slot")
    apply(simp)
    apply(intro conjI impI)
     apply(rule next_child_NoneI)
     apply(simp)
    apply(case_tac xs, simp, simp)
    apply(rule next_childI)
    apply(simp)
   apply(simp)
   apply(fastforce simp: next_child_def intro: next_childI next_child_NoneI)
  apply(simp)
  apply(case_tac "next_child p t")
   apply(simp)
   apply(drule next_child_NoneD)
   apply(rule next_child_NoneI)
   apply(fastforce)
  apply(simp)
  apply(fastforce intro: next_childI dest: next_childD simp: next_child_def)
  done

lemma (in mdb_empty_abs') next_sib_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = None\<rbrakk>
    \<Longrightarrow> next_sib p (t(slot := [])) n
    = (if m p = Some slot then None
      else next_sib p t m)"
  apply(simp, intro conjI impI)
   apply(rule next_sib_NoneI)
   apply(simp add: n_def)
  apply(case_tac "next_sib p t m")
   apply(simp)
   apply(drule next_sib_NoneD)
   apply(erule disjE)
    apply(rule next_sib_NoneI)
    apply(simp add: n_def)
   apply(elim exE conjE)
   apply(rule next_sib_NoneI)
   apply(rule disjI2)
   apply(fastforce simp: n_def)
  apply(fastforce dest: next_sibD intro: next_sibI simp: n_def)
  done


lemma (in mdb_empty_abs') next_sib:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = Some slot_p\<rbrakk>
    \<Longrightarrow> next_sib p (t(slot_p := list_replace_list (t slot_p) slot (t slot), slot := [])) n
     = (if p = slot then None
       else if next_sib p t m = Some slot then
         if t slot = [] then next_sib slot t m
         else next_child slot t
       else if m p = Some slot \<and> after_in_list (t slot) p = None then
         next_sib slot t m
       else next_sib p t m)"
  apply(case_tac "p=slot")
   apply(simp)
   apply(fastforce simp: n_def intro: next_sib_NoneI)
  apply(case_tac "next_sib p t m = Some slot")
   apply(simp, intro conjI impI)
    apply(case_tac "next_sib slot t m")
     apply(simp)
     apply(drule next_sib_NoneD)
     apply(erule disjE)
      apply(fastforce intro: next_sib_NoneI)
     apply(drule next_sibD)
     apply(elim exE conjE)
     apply(rule next_sib_NoneI)
     apply(rule disjI2)
     apply(rule conjI)
      apply(fastforce simp: n_def)
     apply(simp, intro conjI impI)
      apply(simp add: list_replace_empty_after_empty valid_list_2_def)
     apply(drule after_in_list_in_list)
     apply(simp add: valid_list_2_def)
    apply(simp)
    apply(drule next_sibD)+
    apply(elim exE conjE)
    apply(rule next_sibI)
     apply(fastforce simp: n_def)
    apply(simp)
    apply(intro conjI impI notI)
       apply(simp)
      apply(simp add: list_replace_empty_after_empty valid_list_2_def)
     apply(simp)
    apply(drule after_in_list_in_list, simp add: valid_list_2_def)
   apply(drule next_sibD, elim exE conjE)
   apply(case_tac "next_child slot t")
    apply(simp, drule next_child_NoneD)
    apply(rule next_sib_NoneI, simp add: n_def)
   apply(simp, drule(1) next_childD)
   apply(elim exE conjE)
   apply(rule next_sibI)
    apply(simp add: n_def)
    apply(intro conjI impI)
     apply(simp)
    apply(drule after_in_list_in_list)
    apply(simp add: valid_list_2_def)
   apply(simp)
   apply(intro conjI impI notI, simp)
   apply(subst list_replace_after_fst_list)
     apply(frule after_in_list_in_list)
     apply(simp add: valid_list_2_def)
    apply(simp add: valid_list_2_def)
   apply(simp)
  apply(simp)
  apply(intro conjI impI)
   apply(case_tac "next_sib slot t m")
    apply(simp)
    apply(drule next_sib_NoneD)
    apply(erule disjE)
     apply(fastforce simp: n_def intro: next_sib_NoneI)
    apply(elim exE conjE)
    apply(rule next_sib_NoneI)
    apply(rule disjI2)
    apply(rule conjI)
     apply(fastforce simp: n_def)
    apply(simp)
    apply(rule impI)
    apply(drule_tac list="t slot_p" and slot=slot in list_replace_after_None_notin_old)
      apply(simp add: valid_list_2_def)
     apply(simp add: valid_list_2_def)
    apply(simp)
   apply(simp)
   apply(drule next_sibD)
   apply(elim exE conjE)
   apply(rule next_sibI)
    apply(simp add: n_def)
   apply(simp)
   apply(intro conjI impI notI)
    apply simp
   apply(drule_tac list="t slot_p" and slot=slot in list_replace_after_None_notin_old)
     apply(simp add: valid_list_2_def)
    apply(simp add: valid_list_2_def)
   apply(simp)
  apply(case_tac "next_sib p t m")
   apply(simp)
   apply(drule next_sib_NoneD)
   apply(erule disjE)
    apply(fastforce intro: next_sib_NoneI simp: n_def)
   apply(elim exE conjE)
   apply(case_tac "pa=slot")
    apply(fastforce intro: next_sib_NoneI)
   apply(rule_tac p=pa in next_sib_NoneI)
   apply(rule disjI2)
   apply(fastforce simp add: valid_list_2_def n_def list_replace_after_None_notin_new)
  apply(simp)
  apply(drule next_sibD)
  apply(elim exE conjE)
  apply(case_tac "pa=slot")
   apply(rule next_sibI)
    apply(simp add: n_def)
   apply(simp)
   apply(fastforce intro: list_replace_after_notin_old simp: valid_list_2_def)
  apply(simp)
  apply(rule next_sibI)
   apply(simp add: n_def)
  apply(fastforce intro: list_replace_after_notin_new simp: valid_list_2_def)
  done

lemma (in mdb_empty_abs') next_not_child_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list_2 t m; finite_depth m; m slot = None\<rbrakk>
    \<Longrightarrow> next_not_child p (t(slot := [])) n
    = (if (\<exists>sl. next_not_child p t m = Some sl \<and> m sl = Some slot)
        then None
      else next_not_child p t m)"
  apply(simp)
  apply(intro conjI impI)
   apply(elim exE conjE)
   apply(drule(1) next_not_childD, simp add: no_mloop)
   apply(rule next_not_child_NoneI)
     apply(simp add: next_sib_no_parent descendants)
     apply(intro allI impI)
     apply(erule disjE)
      apply(drule next_sibD)
      apply(elim exE conjE)
      apply(drule after_in_list_in_list)
      apply(simp add: valid_list_2_def)
      apply(simp add: descendants_of_def cdt_parent_defs)
      apply(drule tranclD2, simp)
      apply(drule rtranclD, simp)
      apply(drule tranclD2, simp)
     apply(elim conjE exE)
     apply(erule_tac x=q in allE)
     apply(erule impE)
      apply(simp)
      apply(drule next_sibD)
      apply(elim exE conjE)
      apply(drule after_in_list_in_list)
      apply(simp add: valid_list_2_def)
      apply(drule_tac a=p and b=q and c=qa in descendants_linear)
        apply(simp)
       apply(fastforce)
      apply(erule disjE)
       apply(simp)
      apply(simp add: descendants_of_def cdt_parent_defs)
      apply(drule_tac x=q in tranclD2, simp)
      apply(drule rtranclD, simp)
      apply(drule_tac x=q in tranclD2, simp)
     apply(simp)
    apply(simp add: next_sib_no_parent)
    apply(rule impI)
    apply(erule disjE)
     apply(drule next_sibD)
     apply(elim exE conjE)
     apply(drule after_in_list_in_list)
     apply(simp add: valid_list_2_def)
    apply(simp)
   apply(simp add: finite_depth)
  apply(case_tac "next_not_child p t m")
   apply(simp)
   apply(drule(1) next_not_child_NoneD)
   apply(rule next_not_child_NoneI)
     apply(intro allI impI)
     apply(simp add: next_sib_no_parent descendants split: if_split_asm)
    apply(simp add: next_sib_no_parent)
   apply(simp add: finite_depth)
  apply(simp)
  apply(drule(1) next_not_childD, simp add: no_mloop)
  apply(rule next_not_childI)
   apply(erule disjE)
    apply(rule disjI1)
    apply(simp add: next_sib_no_parent)
    apply(drule next_sibD)
    apply(elim exE conjE, drule after_in_list_in_list)
    apply(simp add: valid_list_2_def)
   apply(rule disjI2)
   apply(rule conjI)
    apply(simp add: next_sib_no_parent)
   apply(elim conjE exE)
   apply(rule_tac x=q in exI)
   apply(intro conjI)
     apply(simp add: next_sib_no_parent)
     apply(drule next_sibD)
     apply(elim exE conjE, drule after_in_list_in_list)
     apply(simp add: valid_list_2_def)
    apply(simp add: descendants)
    apply(drule next_sibD)
    apply(elim exE conjE, drule after_in_list_in_list)
    apply(simp add: valid_list_2_def)
    apply(rule conjI)
     apply(fastforce)
    apply(intro notI impI)
    apply(simp)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(drule tranclD2, simp)
   apply(intro allI impI)
   apply(simp add: next_sib_no_parent descendants split: if_split_asm)
  apply(simp add: finite_depth)
  done

lemma (in mdb_empty_abs') next_sib':
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = Some slot_p; t slot = []\<rbrakk>
    \<Longrightarrow> next_sib p (t(slot_p := list_replace_list (t slot_p) slot [], slot := [])) n
     = (if p = slot then None
       else if next_sib p t m = Some slot then
         next_sib slot t m
       else next_sib p t m)"
  apply(insert next_sib)
  apply(atomize)
  apply(erule_tac x=t in allE, erule_tac x=slot_p in allE, erule_tac x=p in allE)
  apply(simp split: if_split_asm)
  apply(simp add: valid_list_2_def)
  apply(erule conjE)
  apply(erule_tac x=slot in allE)
  apply(fastforce)
  done

lemma (in mdb_empty_abs') next_not_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list_2 t m; m slot = Some slot_p; finite_depth m\<rbrakk>
    \<Longrightarrow> next_not_child p (t(slot_p := list_replace_list (t slot_p) slot (t slot), slot := [])) n
     = (if p = slot then None
       else if next_not_child p t m = Some slot then next_slot slot t m
       else next_not_child p t m)"
  apply(case_tac "p=slot")
   apply(simp)
   apply(rule next_not_child_NoneI)
     apply(fastforce simp: next_sib descendants)
    apply(simp add: next_sib)
   apply(simp add: finite_depth)
  apply(case_tac "next_not_child p t m = Some slot")
   apply(simp)
   apply(simp add: next_slot_def)
   apply(intro conjI impI)
    apply(subgoal_tac "\<exists>c. next_child slot t = Some c")
     prefer 2
     apply(case_tac "t slot")
      apply(simp add: next_child_def)
     apply(simp add: next_child_def)
    apply(erule exE)
    apply(simp)
    apply(drule(1) next_not_childD, simp add: no_mloop)
    apply(rule next_not_childI)
     apply(erule disjE)
      apply(simp add: next_sib)
     apply(rule disjI2)
     apply(elim exE conjE)
     apply(subgoal_tac "p \<notin> descendants_of slot m")
      prefer 2
      apply(rule notI)
      apply(drule next_sibD)
      apply(elim exE conjE)
      apply(drule_tac a=p and b=slot and c=q in descendants_linear)
        apply(simp)
       apply(rule notI, simp add: after_in_list_not_self valid_list_2_def)
      apply(drule after_in_list_in_list)
      apply(simp add: valid_list_2_def)
      apply(subgoal_tac "pa \<in> descendants_of pa m")
       prefer 2
       apply(simp add: descendants_of_def cdt_parent_defs)
       apply(erule disjE)
        apply(rule_tac b=q in trancl_into_trancl2)
         apply(simp)
        apply(drule_tac x=q and y=slot in tranclD2)
        apply(simp)
        apply(drule rtranclD)
        apply(fastforce)
       apply(rule_tac b=slot in trancl_into_trancl2)
        apply(simp)
       apply(drule_tac x=slot and y=q in tranclD2)
       apply(simp)
       apply(drule rtranclD)
       apply(fastforce)
      apply(insert valid_mdb)[1]
      apply(drule_tac slot=pa in desc_not_parent, simp add: m_def)
     apply(subgoal_tac "m p \<noteq> Some slot")
      prefer 2
      apply(rule notI)
      apply(fastforce simp: descendants_of_def cdt_parent_defs)
     apply(rule conjI)
      apply(simp add: next_sib)
     apply(rule_tac x=q in exI)
     apply(simp add: descendants)
     apply(intro conjI impI notI)
       apply(simp)
      apply(simp add: next_sib)
     apply(intro allI impI)
     apply(subgoal_tac "m q' \<noteq> Some slot")
      prefer 2
      apply(rule notI)
      apply(drule next_sibD)
      apply(elim exE conjE, drule after_in_list_in_list)
      apply(simp add: valid_list_2_def)
      apply(subgoal_tac "pa \<in> descendants_of pa m")
       prefer 2
       apply(simp add: descendants_of_def cdt_parent_defs)
       apply(rule_tac b=q in trancl_into_trancl2)
        apply(simp)
       apply(elim conjE)
       apply(drule_tac x=q and y=q' in tranclD2)
       apply(simp)
       apply(drule rtranclD)
       apply(simp)
       apply(drule_tac x=q and y=slot in tranclD2)
       apply(simp)
       apply(drule rtranclD)
       apply(fastforce)
      apply(insert valid_mdb)[1]
      apply(drule_tac slot=pa in desc_not_parent, simp add: m_def)
     apply(simp add: next_sib)
    apply(simp add: finite_depth)
   apply(case_tac "next_not_child slot t m")
    apply(simp)
    apply(drule(1) next_not_child_NoneD)
    apply(drule(1) next_not_childD, simp add: no_mloop)
    apply(rule next_not_child_NoneI)
      apply(intro impI allI)
      apply(simp add: next_sib' descendants split: if_split_asm)
      apply(erule disjE)
       apply(drule_tac c=q in next_sib_share_parent, simp)
       apply(fastforce)
      apply(elim conjE exE)
      apply(rule impI)
      apply(drule_tac a=p and b=qa and c=q in descendants_linear)
        apply(simp)
       apply(fastforce)
      apply(erule disjE)
       apply(drule_tac c=q in next_sib_share_parent, simp)
       apply(fastforce)
      apply(fastforce)
     apply(fastforce simp: next_sib')
    apply(simp add: finite_depth)
   apply(simp)
   apply(drule(1) next_not_childD, simp add: no_mloop)+
   apply(elim disjE conjE exE)
      apply(rule next_not_childI)
       apply(simp add: next_sib')
      apply(simp add: finite_depth)
     apply(frule_tac a=p and c=q in next_sib_share_parent, simp)
     apply(rule next_not_childI)
      apply(simp add: next_sib' descendants)
      apply(rule_tac x=q in exI)
      apply(simp)
      apply(frule_tac a=slot and c=a in desc_sib_ne)
         apply(simp)
        apply(simp)
       apply(simp add: no_mloop)
      apply(simp)
      apply(rule conjI)
       apply(rule notI)
       apply(simp add: no_mloop no_mloop_descendants)
      apply(intro impI allI)
      apply(elim conjE)
      apply(drule_tac a=p and c=q' in next_sib_share_parent, simp)
      apply(simp)
     apply(simp add: finite_depth)
    apply(rule next_not_childI)
     apply(simp add: next_sib')
     apply(rule_tac x=q in exI)
     apply(simp add: descendants)
     apply(intro conjI impI allI notI)
      apply(frule next_sibD)
      apply(simp add: not_sib_self)
     apply(simp)
    apply(simp add: finite_depth)
   apply(rule next_not_childI)
    apply(simp add: next_sib')
    apply(rule_tac x=qa in exI)
    apply(simp add: descendants)
    apply(frule_tac a=slot and b=qa and c=a in desc_sib_ne)
       apply(simp)
      apply(simp)
     apply(simp add: no_mloop)
    apply(simp)
    apply(frule_tac a=q and c=qa in next_sib_share_parent)
     apply(simp)
    apply(simp)
    apply(intro conjI impI allI notI)
      apply(simp)
     apply(rule_tac b=q in descendants_trans)
      apply(simp)
     apply(simp)
    apply(erule conjE)
    apply(case_tac "q=q'")
     apply(simp)
    apply(frule_tac a=p and b=q and c=q' in descendants_linear)
      apply(simp)
     apply(simp)
    apply(erule disjE)
     apply(drule_tac a=q and c=q' in next_sib_share_parent)
      apply(simp)
     apply(fastforce)
    apply(fastforce)
   apply(simp add: finite_depth)
  apply(simp)
  apply(case_tac "next_not_child p t m")
   apply(simp)
   apply(drule(1) next_not_child_NoneD)
   apply(erule conjE)
   apply(rule next_not_child_NoneI)
     apply(intro allI impI)
     apply(simp add: next_sib descendants split: if_split_asm)
     apply(intro impI conjI)
      apply(simp add: valid_list_2_def)
      apply(erule conjE)
      apply(erule_tac x=slot in allE)+
      apply(fastforce)
     apply(drule_tac a=p and b=q and c=slot in descendants_trans)
      apply(fastforce simp: descendants_of_def cdt_parent_defs)
     apply(simp)
    apply(simp add: next_sib)
    apply(erule_tac x=slot in allE)
    apply(fastforce simp: descendants_of_def cdt_parent_defs)
   apply(simp add: finite_depth)
  apply(simp)
  apply(drule(1) next_not_childD, simp add: no_mloop)
  apply(erule disjE)
   apply(frule next_sibD)
   apply(rule next_not_childI)
    apply(rule disjI1)
    apply(fastforce simp: next_sib)
   apply(simp add: finite_depth)
  apply(elim conjE exE)
  apply(rule next_not_childI)
   apply(case_tac "q=slot \<and> m p = Some slot")
    apply(rule disjI1)
    apply(simp add: next_sib)
    apply(drule next_sib_NoneD, simp, simp)
   apply(rule disjI2)
   apply(rule conjI)
    apply(simp add: next_sib)
    apply(rule impI)
    apply(erule conjE)
    apply(frule_tac a=p and b=q and c=slot in descendants_linear)
      apply(simp add: child_descendant)
     apply(simp)
    apply(erule disjE)
     apply(simp add: descendants_of_def cdt_parent_defs)
     apply(drule tranclD2, simp)
     apply(drule rtranclD, simp)
     apply(drule_tac x=slot and y=q and z=slot in trancl_trans)
      apply(simp)
     apply(insert no_mloop)[1]
     apply(simp add: no_mloop_def cdt_parent_defs)
    apply(simp add: child_descendant)
   apply(case_tac "q=slot")
    apply(simp)
    apply(subgoal_tac "\<exists>c. m c = Some slot \<and> p \<in> descendants_of c m")
     prefer 2
     apply(simp add: descendants_of_def cdt_parent_defs)
     apply(drule tranclD)
     apply(elim exE conjE)
     apply(rule_tac x=z in exI)
     apply(simp)
     apply(drule rtranclD)
     apply(fastforce)
    apply(elim exE conjE)
    apply(rule_tac x=c in exI)
    apply(rule conjI)
     apply(simp add: next_sib)
     apply(subgoal_tac "next_sib c t m = None")
      prefer 2
      apply(erule_tac x=c in allE)
      apply(erule_tac Q="next_sib c t m = None" in impE)
       apply(simp add: child_descendant)
      apply(simp)
     apply(simp)
     apply(intro conjI impI)
       apply(fastforce)
      apply(fastforce)
     apply(frule_tac slot=c in next_sib_NoneD, simp)
    apply(rule conjI)
     apply(simp add: descendants)
     apply(fastforce)
    apply(intro allI impI)
    apply(simp add: next_sib descendants split: if_split_asm)
    apply(subgoal_tac "next_sib q' t m = None")
     prefer 2
     apply(erule_tac x=q' in allE)
     apply(erule_tac Q="next_sib q' t m = None" in impE)
      apply(simp)
      apply(rule_tac b=c in descendants_trans)
       apply(simp)
      apply(simp add: child_descendant)
     apply(simp)
    apply(simp)
    apply(intro conjI impI notI)
     apply(simp add: valid_list_2_def, erule conjE)
     apply(erule_tac x=slot in allE)+
     apply(fastforce)
    apply(erule conjE)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(drule_tac x=c and y=q' in tranclD2)
    apply(simp)
    apply(drule rtranclD)
    apply(simp)
    apply(drule_tac a=c and b=slot and c=c in trancl_into_trancl)
     apply(simp)
    apply(insert no_mloop)[1]
    apply(simp add: no_mloop_def cdt_parent_defs)
   apply(rule_tac x=q in exI)
   apply(intro conjI)
     apply(simp add: next_sib)
     apply(frule next_sibD)
     apply(intro conjI impI)
     apply(simp)
    apply(simp add: descendants)
   apply(intro allI impI)
   apply(simp add: next_sib descendants split: if_split_asm)
   apply(intro conjI impI)
    apply(simp add: valid_list_2_def, erule conjE)
    apply(erule_tac x=slot in allE)+
    apply(fastforce)
   apply(elim conjE)
   apply(erule_tac x=slot in allE)
   apply(erule impE)
    apply(rule conjI)
     apply(simp add: descendants_of_def cdt_parent_defs)
     apply(drule_tac x=q and y=q' in tranclD2, simp)
     apply(drule rtranclD, simp)
    apply(rule_tac b=q' in descendants_trans)
     apply(simp)
    apply(simp add: child_descendant)
   apply(simp)
  apply(simp add: finite_depth)
  done

lemma (in mdb_empty_abs') next_slot_no_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = None; no_mloop m; finite_depth m\<rbrakk>
    \<Longrightarrow> next_slot p (t(slot := [])) n
     = (if p = slot then None
       else if (\<exists>sl. next_slot p t m = Some sl \<and> m sl = Some slot)
         then None
       else next_slot p t m)"
  apply(case_tac "p=slot")
   apply(simp add: next_slot_def next_not_child_no_parent)
   apply(rule impI)
   apply(simp add: next_not_child_termination next_sib_def)
  apply(case_tac "\<exists>sl. next_slot p t m = Some sl \<and> m sl = Some slot")
   apply(simp add: next_slot_def)
   apply(intro conjI impI)
    apply(elim exE conjE)
    apply(simp split: if_split_asm)
    apply(drule(1) next_childD)
    apply(simp)
   apply(simp add: next_not_child_no_parent)
  apply(simp only:, simp)
  apply(simp add: next_slot_def next_child_no_parent next_not_child_no_parent)
  apply(fastforce split: if_split_asm)
  done

lemma (in mdb_empty_abs') next_slot:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_list_2 t m; m slot = Some slot_p; no_mloop m; finite_depth m\<rbrakk>
    \<Longrightarrow> next_slot p (t(slot_p := list_replace_list (t slot_p) slot (t slot), slot := [])) n
     = (if p = slot then None
       else if next_slot p t m = Some slot then next_slot slot t m
       else next_slot p t m)"
  apply(case_tac "p=slot")
   apply(simp add: next_slot_def next_not_child next_child)
  apply(case_tac "next_slot p t m = Some slot")
   apply(simp only: next_slot_def next_not_child next_child)
   apply(case_tac "t slot = []")
    apply(simp split del: if_split)
    apply(case_tac "t p = []")
     apply(fastforce)
    apply(case_tac "p=slot_p \<and> t slot_p = [slot]")
     apply(simp)
     apply(rule impI)
     apply(subgoal_tac "next_not_child_dom (slot, t, m)")
      prefer 2
      apply(simp add: next_not_child_termination valid_list_2_def)
     apply(simp)
     apply(rule impI, erule exE)
     apply(frule_tac src=slot in next_sib_not_self)
     apply(drule next_sibD)
     apply(fastforce)
    apply(simp split del: if_split)
    apply(case_tac "p = slot_p")
     apply(subgoal_tac "list_replace_list (t slot_p) slot [] \<noteq> []")
      prefer 2
      apply(case_tac "t slot_p")
       apply(simp)
      apply(simp add: valid_list_2_def)
     apply(simp split del: if_split)
     apply(simp)
     apply(intro conjI impI)
      apply(case_tac "t slot_p")
       apply(simp)
      apply(simp)
      apply(case_tac list)
       apply(simp)
      apply(simp)
      apply(rule next_not_childI[symmetric])
       apply(simp add: next_sib_def)
      apply(simp)
     apply(case_tac "t slot_p")
      apply(simp)
     apply(simp add: next_child_def)
    apply(simp)
    apply(rule conjI)
     apply(rule impI)
     apply(case_tac "t p")
      apply(simp)
     apply(simp add: valid_list_2_def)
     apply(erule conjE)
     apply(erule_tac x=p in allE)
     apply(simp add: set_eq_subset)
    apply(intro conjI impI)
     apply(fastforce simp: valid_list_2_def)
    apply(case_tac "t p")
     apply(simp)
    apply(simp add: next_child_def)
   apply(simp split del: if_split)
   apply(case_tac "t p")
    apply(fastforce)
   apply(case_tac "t p = [slot]")
    apply(fastforce)
   apply(fastforce split: if_split_asm)
  apply(simp)
  apply(simp add: next_slot_def split del: if_split)
  apply(case_tac "t p")
   apply(fastforce simp: next_not_child next_child)
  apply(case_tac "t p = [slot]")
   apply(simp add: next_not_child next_child next_child_def)
  apply(simp add: next_child next_not_child)
  apply(fastforce split: if_split_asm)
  done

crunch valid_list[wp]: post_cap_deletion,set_cap valid_list
  (wp: crunch_wps)

interpretation empty_slot_extended: is_extended "empty_slot_ext a b"
  by (unfold_locales; wp)


lemma empty_slot_valid_list[wp]:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrace>valid_list\<rbrace>
     empty_slot sl irqopt
   \<lbrace>\<lambda>rv. valid_list\<rbrace>"
  supply if_cong[cong]
  apply (simp add: empty_slot_def)
  apply (simp add: set_cdt_def update_cdt_list_def set_cdt_list_def
                   empty_slot_ext_def bind_assoc cong: if_cong)
  apply (wp get_cap_wp static_imp_wp | wpc | wp (once) hoare_vcg_all_lift)+
  apply (clarsimp simp del: fun_upd_apply)
  apply (frule mdb_empty_abs_simple.intro)
  apply(case_tac "cdt s sl")
   apply (frule(1) mdb_empty_abs_simple.valid_list_post_no_parent)
   apply simp
  apply (case_tac "a = sl")
   apply (frule(2) mdb_empty_abs_simple.valid_list_post_self_parent)
   apply simp
  apply (frule(2) mdb_empty_abs_simple.valid_list_post)
  apply simp
  done

lemma set_cap_exst_update:
  "((),s') \<in> fst (set_cap c p s) \<Longrightarrow> ((),exst_update f s') \<in> fst (set_cap c p (exst_update f s))"
  apply (cases p)
  apply (clarsimp simp add: set_cap_def in_monad get_object_def)
  apply (rename_tac obj; case_tac obj)
      apply (auto simp: in_monad set_object_def get_object_def
                 split: if_split_asm kernel_object.splits)
  done

lemma no_parent_not_next_slot:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>m slot = None; valid_list_2 t m; finite_depth m; no_mloop m\<rbrakk>
          \<Longrightarrow> next_slot p t m \<noteq> Some slot"
  apply(rule notI)
  apply(simp add: next_slot_def split: if_split_asm)
   apply(drule(1) next_childD)
   apply(simp)
  apply(drule(2) next_not_childD)
  apply(erule disjE)
   apply(drule next_sibD)
   apply(elim exE conjE)
   apply(drule after_in_list_in_list)
   apply(simp add: valid_list_2_def)
  apply(elim conjE exE)
  apply(drule next_sibD)
  apply(elim exE conjE)
  apply(drule after_in_list_in_list)
  apply(simp add: valid_list_2_def)
  done


definition descendants_prop where
 "descendants_prop P t \<equiv> (\<forall>p. \<forall>c \<in> set (t p). P c)"

locale mdb_swap_abs_simple =
 fixes m :: cdt
 fixes t t' t'' n' n dest src
 defines "n' \<equiv>
     \<lambda>n. if m n = Some src then Some dest
         else if m n = Some dest then Some src else m n"
    and "n \<equiv> n'(src := n' dest, dest := n' src)"
 defines "t' \<equiv> (case n src of
      None \<Rightarrow> (case n dest of
        None \<Rightarrow> t'' |
        Some dest_p \<Rightarrow> t'' (dest_p := list_replace (t'' dest_p) src dest)) |
      Some src_p \<Rightarrow> (case n dest of
        None \<Rightarrow> t'' (src_p := list_replace (t'' src_p) dest src) |
        Some dest_p \<Rightarrow> if src_p = dest_p
          then t'' (src_p := list_swap (t'' src_p) src dest)
          else t'' (src_p := list_replace (t'' src_p) dest src,
                     dest_p := list_replace (t'' dest_p) src dest)))"
  defines "t'' \<equiv> t(src := t dest, dest := t src)"
 assumes valid_list: "valid_list_2 t m"
begin



lemma valid_list_post_no_parents:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "m src = None \<Longrightarrow> m dest = None \<Longrightarrow> valid_list_2 t' n"
  apply (insert valid_list)
  apply (simp add: t'_def t''_def n_def n'_def valid_list_2_def)
  apply (intro impI conjI allI)
  apply fastforce+
  done

lemma valid_list_post_src_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "m src = Some src_p \<Longrightarrow> m dest = None \<Longrightarrow> valid_list_2 t' n"
  apply (insert valid_list)
  apply (simp add: t'_def t''_def n_def n'_def)
  apply (intro impI conjI allI)
  apply (fastforce simp: valid_list_2_def replace_distinct list_replace_set)+
  done

lemma valid_list_post_dest_parent:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "m src = None \<Longrightarrow> m dest = Some dest_p \<Longrightarrow> valid_list_2 t' n"
  apply (insert valid_list)
  apply (simp add: t'_def t''_def n_def n'_def)
  apply (intro impI conjI allI)
  apply (fastforce simp: valid_list_2_def replace_distinct list_replace_set)+
  done

lemma valid_list_post_parents:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "m src = Some src_p \<Longrightarrow> m dest = Some dest_p \<Longrightarrow> valid_list_2 t' n"
  apply (insert valid_list)
  apply (simp add: t'_def t''_def n_def n'_def)
  apply (intro impI conjI allI)
  apply (simp add: valid_list_2_def list_swap_def swap_distinct[simplified list_swap_def] list_replace_def replace_distinct[simplified list_replace_def]| intro impI conjI allI | fastforce)+
  done

lemma valid_list_post:
  "valid_list_2 t' n"
  apply (case_tac "m src")
  apply (case_tac "m dest")
    apply (simp add: valid_list_post_no_parents)
   apply (simp add: valid_list_post_dest_parent)
  apply (case_tac "m dest")
   apply (simp add: valid_list_post_src_parent)
  apply (simp add: valid_list_post_parents)
  done

end

locale mdb_swap_abs'' = mdb_swap_abs + constrains s::"det_state"

locale mdb_swap_abs' = mdb_swap_abs'' +
  fixes t t' t''
  defines "t' \<equiv> (case n src of
      None \<Rightarrow> (case n dest of
        None \<Rightarrow> t'' |
        Some dest_p \<Rightarrow> t'' (dest_p := list_replace (t'' dest_p) src dest)) |
      Some src_p \<Rightarrow> (case n dest of
        None \<Rightarrow> t'' (src_p := list_replace (t'' src_p) dest src) |
        Some dest_p \<Rightarrow> if src_p = dest_p
          then t'' (src_p := list_swap (t'' src_p) src dest)
          else t'' (src_p := list_replace (t'' src_p) dest src,
                     dest_p := list_replace (t'' dest_p) src dest)))"
  defines "t'' \<equiv> t(src := t dest, dest := t src)"
  assumes "t = cdt_list s"
  assumes valid_list: "valid_list_2 t m"

context mdb_swap_abs'
begin

lemma findepth:
  "finite_depth m"
  apply (simp add: m)
  apply (rule Deterministic_AI.finite_depth)
  apply (rule valid_mdb)
  done

lemma finite_depth:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "finite_depth n"
  apply (insert findepth)
  apply(simp add: finite_depth_def descendants split del: if_split)
  apply(simp add: n_def n'_def split del: if_split)
  apply(rule allI)
  apply(case_tac "slot=src")
   apply(erule_tac x=dest in allE)
   apply(elim exE conjE)
   apply(case_tac "p=src")
    apply(rule_tac x=dest in exI, simp add: s_d_swap_def)
   apply(case_tac "p = dest")
    apply(rule_tac x ="src" in exI, simp add: s_d_swap_def)
   apply(rule_tac x=p in exI, simp add: s_d_swap_def)
  apply (case_tac "slot=dest")
   apply(erule_tac x=src in allE)
   apply (elim exE conjE)
   apply (case_tac "p=src")
    apply (rule_tac x =dest in exI, simp add: s_d_swap_def)
   apply (case_tac "p=dest")
    apply (simp add: descendants_of_def)
    apply (intro conjI impI)
     apply (rule_tac x = "src" in exI, intro conjI, rule impI, simp+)
    apply (rule_tac x = "src" in exI)
    apply (intro conjI impI; simp)
   apply (rule_tac x = "p" in exI)
   apply (simp add: descendants_of_def s_d_swap_def)
  apply (erule_tac x = slot in allE)
  apply (elim exE conjE)
  apply (case_tac "p = dest")
   apply (rule_tac x = "src" in exI, simp add: descendants_of_def s_d_swap_def)
  apply (case_tac "p = src")
   apply (rule_tac x = "dest" in exI, simp add: descendants_of_def s_d_swap_def)
  apply (rule_tac x ="p" in exI, simp add: descendants_of_def s_d_swap_def)
  done

lemma parency_antisym: "\<And>x y. m x = Some y \<Longrightarrow> m y \<noteq> Some x"
  apply (frule parent_not_descendant[OF no_mloop])
  apply (rule notI)
  apply (frule_tac src=y and src_p=x in child_descendant,simp)
  done

lemma parent_not_next_child: "x \<notin> set (t x)"
  apply (insert no_mloop valid_list)
  apply (simp add: valid_list_2_def no_mloop_def del: split_paired_All)
  done

lemma valid_list_post:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes parency_antisym[where x=src and y = dest,simp]
  notes parent_not_next_child[simp]
  shows "valid_list_2 t' n"
  proof -
    from valid_list show ?thesis
    supply if_weak_cong[cong del]
    apply (simp add: t'_def t''_def n_def n'_def cong: option.case_cong)
    by (simp add: replace_distinct[OF parent_not_next_child]
                     replace_distinct list_replace_set
                     list_swap_both insert_Collect remove_collect
                     swap_distinct
           | intro impI conjI iffI allI
           | (intro impI conjI iffI notI,simp_all)
           | rule Collect_cong
           | simp split: option.splits
           | (rule ccontr,simp,elim impE,rule notI)
           | simp only: valid_list_2_def  )+ (*slow*)
qed

lemma next_child_antisym: "next_child x t = Some y \<Longrightarrow> next_child y t \<noteq> Some x"
  apply (rule notI)
  apply (clarsimp dest!: next_childD[OF _ valid_list])
  apply (simp add: parency_antisym)
  done

lemma next_childI'': "(\<exists>xs. t''' slot = child # xs) \<Longrightarrow> next_child slot t''' = Some child"
  apply (elim exE)
  apply (rule next_childI,simp)
  done

lemma next_childD'':
 notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
"next_child slot t''' \<noteq> Some child \<Longrightarrow> t''' slot = [] \<or> (\<exists>xs a. t''' slot = a#xs \<and> a \<noteq> child)"
  apply (simp add: next_child_def)
  apply (case_tac "t''' slot")
  apply simp+
  done

lemma next_child_eq_ignore: "g p = g' p \<Longrightarrow> next_child p g = next_child p g'"
  by(simp add: next_child_def)

lemma next_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes parency_antisym[where x=src and y = dest,simp]
  notes next_child_antisym[where x=src and y = dest,simp]
  notes next_childD' = next_childD[OF _ valid_list]
  notes rdefs = t'_def t''_def n_def n'_def
  shows
  "next_child p t'
    = (if p = src then
        (if next_child dest t = Some src then Some dest
         else next_child dest t)
      else if p = dest then
        (if next_child src t = Some dest then Some src
         else next_child src t)
      else if next_child p t = Some src then Some dest
      else if next_child p t = Some dest then Some src
      else next_child p t)"
  apply (simp add: rdefs split: option.splits)
  apply (intro impI conjI,simp_all)
  by ((intro impI conjI allI | drule next_child_NoneD next_childD'  next_childD'' |
       rule next_childI'' | simp add: list_replace_def list_swap_def | elim exE conjE disjE |
       simp add: next_child_def)+) (*slow*)


lemma next_sib_antisym:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "next_sib x t m = Some y \<Longrightarrow> next_sib y t m \<noteq> Some x"
  apply (rule notI)
  apply (frule next_sib_same_parent[OF valid_list])
  apply (elim exE conjE)
  apply (drule next_sibD)+
  apply (elim exE conjE)
  apply (simp add: valid_list[simplified valid_list_2_def] distinct_after_in_list_antisym)
  done


lemma after_in_listD': "after_in_list (t p) x = Some y \<Longrightarrow> (\<exists>xs ys. xs @ (x # y # ys) = (t p) \<and> x \<notin> set xs) \<and> (m y = Some p \<and> m x = Some p) \<and> x \<noteq> y"
  apply (rule conjI)
  apply (drule after_in_listD)
  apply force
  apply (drule after_in_listD)
  apply (elim exE conjE)
  apply (rule conjI)
  apply (subgoal_tac "x \<in> set (t p) \<and> y \<in> set (t p)")
  apply (thin_tac "t p = Q" for Q)
  apply (simp add: valid_list[simplified valid_list_2_def])+
  apply (subgoal_tac "distinct (t p)")
  apply simp
  apply (thin_tac "t p = Q" for Q)
  apply (simp add: valid_list[simplified valid_list_2_def])+
  done

lemma optionD: "x \<noteq> Some y \<Longrightarrow> x = None \<or> (\<exists>z. x = Some z \<and> z \<noteq> y)"
  by (case_tac "x"; simp)

lemma t_distinct: "distinct (t x)"
  by (simp add: valid_list[simplified valid_list_2_def])

lemma t_some[simp]: "set (t x) = {c. m c = Some x}"
  by (simp add: valid_list[simplified valid_list_2_def])

declare t_distinct [simp]

lemmas list_swap_preservation_t =
  list_swap_preserve_after list_swap_preserve_after'
  list_swap_preserve_after'' list_swap_preserve_None list_swap_preserve_None'
  list_swap_preserve_Some_other' list_swap_preserve_Some_other_distinct[OF t_distinct]
  list_swap_preserve_Some_other_distinct[OF t_distinct, simplified list_swap_symmetric]
  list_swap_does_swap[OF t_distinct]
  list_swap_does_swap[OF t_distinct,simplified list_swap_symmetric]
  list_swap_preserve_after_None list_swap_preserve_separate list_swap_does_swap'

lemma next_sibD':
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "next_sib slot t m = Some child \<Longrightarrow>
         \<exists>p. m slot = Some p \<and> m child = Some p \<and> after_in_list (t p) slot = Some child"
  apply (frule next_sib_same_parent[OF valid_list])
  apply (drule next_sibD)
  apply clarsimp
  done

lemma next_sib:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  notes parency_antisym[where x=src and y = dest,simp]
  notes next_sib_antisym[where x=src and y = dest,simp]
  notes distinct_after_in_list_not_self[OF t_distinct,simp]
  notes rdefs = t'_def t''_def n_def n'_def
  notes parent_not_next_child[simp]
  shows
  "next_sib p t' n
    = (if p = src then
        (if next_sib dest t m = Some src then Some dest
         else next_sib dest t m)
      else if p = dest then
        (if next_sib src t m = Some dest then Some src
         else next_sib src t m)
      else if next_sib p t m = Some src then Some dest
      else if next_sib p t m = Some dest then Some src
      else next_sib p t m)"
  supply if_cong[cong]
  apply simp
  apply (intro impI conjI allI,simp_all)
  by ((intro impI conjI allI
   | drule next_sib_NoneD next_sibD'
   | simp add: next_sib_def rdefs split: option.splits
   | simp add: after_in_list_append_notin_hd replace_list_preserve_after replace_list_preserve_after'
               list_swap_preservation_t replace_distinct swap_distinct
   | rule after_in_list_list_replace
   | drule optionD after_in_listD'
   | elim exE conjE disjE | force )+) (*slow*)

lemma next_not_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "next_not_child p t' n
    = (if p = src then
        (if next_not_child dest t m = Some src then Some dest
         else next_not_child dest t m)
      else if p = dest then
        (if next_not_child src t m = Some dest then Some src
         else next_not_child src t m)
      else if next_not_child p t m = Some src then Some dest
      else if next_not_child p t m = Some dest then Some src
      else next_not_child p t m)"
  apply(case_tac "p=src")
   apply(case_tac "next_not_child dest t m = Some src")
    apply(simp)
    apply(drule next_not_childD, simp add: findepth, simp add: no_mloop)
    apply(rule next_not_childI)
     apply(erule disjE)
      apply(simp add: next_sib)
     apply(elim conjE exE)
     apply(rule disjI2)
     apply(simp add: next_sib)
     apply(intro impI conjI)
      apply(drule next_sibD')+
      apply(simp add: descendants_of_def cdt_parent_defs)
      apply(case_tac "m q", simp)
      apply(case_tac "m src", simp)
      apply(simp)
      apply(drule tranclD2)
      apply(simp)
      apply(drule_tac a=q and b=a and c=q in rtrancl_into_trancl1)
       apply(simp)
      apply(insert no_mloop)[1]
      apply(simp add: no_mloop_def cdt_parent_defs)
     apply(case_tac "q=src")
      apply(rule_tac x=dest in exI)
      apply(simp)
      apply(simp add: not_sib_self valid_list)
     apply(rule_tac x=q in exI)
     apply(simp)
     apply(intro conjI impI notI allI)
            apply(simp add: descendants s_d_swap_def split: if_split_asm)+
    apply(simp add: finite_depth)
   apply(simp)
   apply(case_tac "next_not_child dest t m")
    apply(simp)
    apply(drule next_not_child_NoneD, simp add: findepth)
    apply(rule next_not_child_NoneI)
      apply(simp add: next_sib descendants s_d_swap_def)
     apply(simp add: next_sib)
    apply(simp add: finite_depth)
   apply(simp)
   apply(drule next_not_childD, simp add: findepth, simp add: no_mloop)
   apply(rule next_not_childI)
    apply(erule disjE)
     apply(simp add: next_sib)
    apply(elim conjE exE)
    apply(rule disjI2)
    apply(simp add: next_sib split del: if_split)
    apply(case_tac "q=src")
     apply(rule_tac x=dest in exI)
     apply(simp add: descendants s_d_swap_def)
     apply(insert no_mloop)[1]
     apply(intro conjI impI notI allI)
              apply((simp add: no_mloop_def descendants_of_def)+)[7]
       apply(drule(1) desc_sib_ne, simp add: valid_list, simp, simp)
      apply(simp)
     apply(simp)
    apply(rule_tac x=q in exI)
    apply(subgoal_tac "q\<noteq>dest")
     prefer 2
     apply(rule notI)
     apply(insert valid_mdb)[1]
     apply(drule_tac slot=dest in desc_not_parent, simp)
    apply(subgoal_tac "a\<noteq>dest")
     prefer 2
     apply(rule notI, simp)
     apply(drule(1) desc_sib_ne, simp add: valid_list, simp add: no_mloop, simp)
    apply(simp add: descendants s_d_swap_def split del: if_split)
    apply(simp)
    apply(intro conjI impI allI notI, simp+)
   apply(simp add: finite_depth)
  apply(case_tac "p=dest")
   apply(case_tac "next_not_child src t m = Some dest")
    apply(simp)
    apply(drule next_not_childD, simp add: findepth, simp add: no_mloop)
    apply(rule next_not_childI)
     apply(erule disjE)
      apply(simp add: next_sib)
     apply(elim conjE exE)
     apply(rule disjI2)
     apply(simp add: next_sib)
     apply(intro impI conjI)
      apply(drule next_sibD')+
      apply(simp add: descendants_of_def cdt_parent_defs)
      apply(case_tac "m q", simp)
      apply(case_tac "m dest", simp)
      apply(simp)
      apply(drule tranclD2)
      apply(simp)
      apply(drule_tac a=q and b=a and c=q in rtrancl_into_trancl1)
       apply(simp)
      apply(insert no_mloop)[1]
      apply(simp add: no_mloop_def cdt_parent_defs)
     apply(case_tac "q=dest")
      apply(rule_tac x=src in exI)
      apply(simp add: not_sib_self valid_list)
     apply(rule_tac x=q in exI)
     apply(simp)
     apply(intro conjI impI notI allI)
            apply(simp add: descendants s_d_swap_def split: if_split_asm)+
    apply(simp add: finite_depth)
   apply(simp)
   apply(case_tac "next_not_child src t m")
    apply(simp)
    apply(drule next_not_child_NoneD, simp add: findepth)
    apply(rule next_not_child_NoneI)
      apply(simp add: next_sib descendants s_d_swap_def)
     apply(simp add: next_sib)
    apply(simp add: finite_depth)
   apply(simp)
   apply(drule next_not_childD, simp add: findepth, simp add: no_mloop)
   apply(rule next_not_childI)
    apply(erule disjE)
     apply(simp add: next_sib)
    apply(elim conjE exE)
    apply(rule disjI2)
    apply(simp add: next_sib split del: if_split)
    apply(case_tac "q=dest")
     apply(rule_tac x=src in exI)
     apply(simp add: descendants s_d_swap_def)
     apply(insert no_mloop)[1]
     apply(intro conjI impI notI allI)
              apply((simp add: no_mloop_def descendants_of_def)+)[7]
       apply(drule(1) desc_sib_ne, simp add: valid_list, simp, simp)
      apply(simp)
     apply(simp)
    apply(rule_tac x=q in exI)
    apply(subgoal_tac "q\<noteq>src")
     prefer 2
     apply(rule notI)
     apply(insert valid_mdb)[1]
     apply(drule_tac slot=src in desc_not_parent, simp)
    apply(subgoal_tac "a\<noteq>src")
     prefer 2
     apply(rule notI, simp)
     apply(drule(1) desc_sib_ne, simp add: valid_list, simp add: no_mloop, simp)
    apply(simp add: descendants s_d_swap_def split del: if_split)
    apply(simp)
    apply(intro conjI impI allI notI, simp+)
   apply(simp add: finite_depth)
  apply(case_tac "next_not_child p t m = Some src")
   apply(simp)
   apply(drule next_not_childD, simp add: findepth, simp add: no_mloop)
   apply(rule next_not_childI)
    apply(erule disjE)
     apply(simp add: next_sib)
    apply(rule disjI2)
    apply(elim conjE exE)
    apply(subst next_sib, simp)
    apply(case_tac "q=dest")
     apply(rule_tac x=src in exI)
     apply(simp add: next_sib descendants s_d_swap_def split del: if_split)
     apply(intro allI impI)
     apply(simp)
     apply(simp split: if_split_asm)
    apply(rule_tac x=q in exI)
    apply(subgoal_tac "q\<noteq>src")
     prefer 2
     apply(rule notI)
     apply(simp add: not_sib_self valid_list)
    apply(intro conjI allI impI)
      apply(simp add: next_sib)
     apply(simp add: descendants s_d_swap_def)
    apply(simp add: next_sib)
    apply(subgoal_tac "next_sib dest t m \<noteq> Some src")
     prefer 2
     apply(rule notI)
     apply(drule_tac a=q and b=dest in next_sib_inj, simp, simp add: valid_list, simp)
    apply(case_tac "q'=dest")
     apply(simp add: descendants s_d_swap_def split: if_split_asm)
    apply(simp add: descendants s_d_swap_def split: if_split_asm)
   apply(simp add: finite_depth)
  apply(case_tac "next_not_child p t m = Some dest")
   apply(simp)
   apply(drule next_not_childD, simp add: findepth, simp add: no_mloop)
   apply(rule next_not_childI)
    apply(erule disjE)
     apply(simp add: next_sib)
    apply(rule disjI2)
    apply(elim conjE exE)
    apply(subst next_sib, simp)
    apply(case_tac "q=src")
     apply(rule_tac x=dest in exI)
     apply(simp add: next_sib descendants s_d_swap_def split del: if_split)
     apply(intro allI impI)
     apply(simp)
     apply(simp split: if_split_asm)
    apply(rule_tac x=q in exI)
    apply(subgoal_tac "q\<noteq>dest")
     prefer 2
     apply(rule notI)
     apply(simp add: not_sib_self valid_list)
    apply(intro conjI allI impI)
      apply(simp add: next_sib)
     apply(simp add: descendants s_d_swap_def)
    apply(simp add: next_sib)
    apply(subgoal_tac "next_sib src t m \<noteq> Some dest")
     prefer 2
     apply(rule notI)
     apply(drule_tac a=q and b=src in next_sib_inj, simp, simp add: valid_list, simp)
    apply(case_tac "q'=src")
     apply(simp add: descendants s_d_swap_def split: if_split_asm)
    apply(simp add: descendants s_d_swap_def split: if_split_asm)
   apply(simp add: finite_depth)
  apply(simp)
  apply(case_tac "next_not_child p t m")
   apply(simp)
   apply(drule next_not_child_NoneD, simp add: findepth)
   apply(rule next_not_child_NoneI)
     apply(simp add: descendants s_d_swap_def next_sib split del: if_split)
     apply(intro allI conjI)
       apply(simp_all)[3]
    apply(simp add: next_sib)
   apply(simp add: finite_depth)
  apply(simp)
  apply(drule next_not_childD, simp add: findepth, simp add: no_mloop)
  apply(rule next_not_childI)
   apply(erule disjE)
    apply(simp add: next_sib)
   apply(rule disjI2)
   apply(rule conjI)
    apply(simp add: next_sib)
   apply(elim conjE exE)
   apply(case_tac "q=dest")
    apply(rule_tac x=src in exI)
    apply(intro conjI impI allI)
      apply(simp add: next_sib)
     apply(simp add: descendants s_d_swap_def)
    apply(simp add: next_sib descendants s_d_swap_def split: if_split_asm)
   apply(case_tac "q=src")
    apply(rule_tac x=dest in exI)
    apply(intro conjI impI allI)
      apply(simp add: next_sib)
     apply(simp add: descendants s_d_swap_def)
    apply(simp add: next_sib descendants s_d_swap_def split: if_split_asm)
   apply(rule_tac x=q in exI)
   apply(intro conjI impI allI)
     apply(simp add: next_sib)
    apply(simp add: descendants s_d_swap_def)
   apply(simp add: next_sib descendants s_d_swap_def split: if_split_asm)
  apply(simp add: finite_depth)
  done

lemma t'_empty:
  "(t' src = []) = (t dest = [])"
  "(t' dest = []) = (t src = [])"
  "p\<noteq>src \<and> p\<noteq>dest \<Longrightarrow> (t' p = []) = (t p = [])"
  by(fastforce simp: n_def n'_def t''_def t'_def list_swap_def
              split: option.splits split: if_split_asm)+

lemma next_slot:
  "next_slot p t' n
    = (if p = src then
        (if next_slot dest t m = Some src then Some dest
         else next_slot dest t m)
      else if p = dest then
        (if next_slot src t m = Some dest then Some src
         else next_slot src t m)
      else if next_slot p t m = Some src then Some dest
      else if next_slot p t m = Some dest then Some src
      else next_slot p t m)"
  apply(case_tac "p=src")
   apply(simp add: next_slot_def next_child next_not_child valid_list t'_empty)
  apply(case_tac "p=dest")
   apply(simp add: next_slot_def next_child next_not_child valid_list t'_empty
         split: if_split_asm)
  apply(case_tac "next_slot p t m = Some src")
   apply(simp add: next_slot_def next_child next_not_child s_d_swap_def t'_empty
         split: if_split_asm)
  apply(case_tac "next_slot p t m = Some dest")
   apply(simp add: next_slot_def next_child next_not_child s_d_swap_def  t'_empty
         split: if_split_asm)
  apply(simp add: next_slot_def next_child next_not_child s_d_swap_def t'_empty
        split: if_split_asm)
  done

end


interpretation cap_swap_ext_extended: is_extended "cap_swap_ext a b c d"
  by (unfold_locales; wp cap_swap_ext_all_but_exst)


lemma cap_swap_valid_list [wp]:
  "\<lbrace>valid_list\<rbrace>
  cap_swap c a c' b
  \<lbrace>\<lambda>_. valid_list\<rbrace>"
  supply if_weak_cong[cong del]
  apply (simp only: cap_swap_def cap_swap_ext_extended.dxo_eq)
  apply (simp only: cap_swap_ext_def update_cdt_list_def set_cdt_list_def set_cdt_def bind_assoc)
  apply wp
  apply (simp del: fun_upd_apply split del: if_split cong: option.case_cong)
        apply (wp set_cap_caps_of_state3)+
  apply (case_tac "a = b")
   apply (simp split: option.splits)
  apply(subgoal_tac "mdb_swap_abs_simple (cdt s) (cdt_list s)")
   prefer 2
   apply(rule mdb_swap_abs_simple.intro)
   apply simp
  apply(frule mdb_swap_abs_simple.valid_list_post[where src=a and dest=b])
  apply(simp add: fun_upd_def split del: if_split cong: option.case_cong)
  done


lemma exst_set_cap:
  "(x,s') \<in> fst (set_cap p c s) \<Longrightarrow> exst s' = exst s"
  by (erule use_valid[OF _ set_cap_exst],simp)

interpretation create_cap_extended: is_extended "create_cap_ext a b c"
  by (unfold_locales; wp)

lemma create_cap_valid_list[wp]:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrace>valid_list \<rbrace>
      create_cap tp sz p dev x \<lbrace>\<lambda>rv. valid_list\<rbrace>"
  apply (case_tac x)
  apply (simp add: create_cap_def)
  apply(simp add: set_cdt_def update_cdt_list_def set_cdt_list_def create_cap_ext_def bind_assoc)
  apply (rule hoare_pre)
   apply (simp add: valid_list_2_def)
   apply (wp | simp cong: option.case_cong if_cong del: fun_upd_apply split del: if_split)+
         apply(wp set_cap_caps_of_state3 get_cap_wp)+
  apply(simp del: fun_upd_apply split: option.splits split del: if_split cong:if_weak_cong)
  apply (intro impI conjI allI)
     apply (simp add: valid_list_2_def | intro impI conjI allI | fastforce simp: list_remove_removed list_remove_distinct)+
  done


crunch valid_list[wp]: set_extra_badge valid_list

lemmas transfer_caps_loop_ext_valid[wp] =
  transfer_caps_loop_pres[OF cap_insert_valid_list set_extra_badge_valid_list]

crunch valid_list[wp]: tcb_sched_action,reschedule_required,tcb_release_remove "valid_list"
  (simp: unless_def thread_get_def crunch_simps wp: hoare_drop_imp)

crunch valid_list[wp]: schedule_tcb "valid_list"
  (simp: unless_def)

lemma set_simple_ko_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> set_simple_ko f p v \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: set_simple_ko_def wp: hoare_drop_imp)

lemma update_sk_obj_ref_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> update_sk_obj_ref C f p v \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def)

crunch valid_list[wp]: set_thread_state valid_list

lemma update_sched_context_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> update_sched_context ptr sc \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: update_sched_context_def wp: hoare_drop_imp)

lemma set_tcb_obj_ref_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> set_tcb_obj_ref f r v \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def wp: hoare_drop_imp)

lemma reply_unlink_tcb_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def wp: hoare_drop_imp)

lemma reply_unlink_sc_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> reply_unlink_sc sc r \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def wp: hoare_drop_imp)

(* locale for valid_list proofs *)
locale non_cdt_cdt_list_op =
  fixes f
  assumes cdt_cdt_list[wp]:
     "\<And>P. \<lbrace>\<lambda>s. P (cdt s)(cdt_list s)\<rbrace> f \<lbrace>\<lambda>_ s. P (cdt s)(cdt_list s)\<rbrace>"
begin

lemma valid_list[wp]: "\<lbrace>valid_list\<rbrace> f \<lbrace>\<lambda>_. valid_list\<rbrace>"
  by wp

end

lemma set_scheduler_action_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> set_scheduler_action action \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: set_scheduler_action_def)

lemma set_tcb_queue_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> set_tcb_queue d prio queue \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: set_tcb_queue_def)

lemma tcb_sched_action_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> tcb_sched_action action thread \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: tcb_sched_action_def thread_get_def)

lemma tcb_release_remove_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> tcb_release_remove t \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: tcb_release_remove_def)

lemma reschedule_required_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> reschedule_required \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: reschedule_required_def thread_get_def wp: hoare_drop_imp)

lemma test_reschedule_cdt_cdt_list[wp]:
   "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> test_reschedule r \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: test_reschedule_def
       wp: hoare_drop_imps)

crunch (empty_fail) empty_fail[wp]: test_reschedule,tcb_release_remove

(*
interpretation
  test_reschedule: non_cdt_cdt_list_op "test_reschedule r"
  by (unfold_locales; wp)
*)
lemma sched_context_donate_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> sched_context_donate sc_ptr tcb_ptr\<lbrace>\<lambda>_.valid_list\<rbrace>"
  supply if_cong[cong]
  by (wpsimp simp: sched_context_donate_def set_tcb_obj_ref_def
      wp: get_sc_obj_ref_inv hoare_drop_imp)

lemma schedule_tcb_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> schedule_tcb p \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)

lemma set_thread_state_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> set_thread_state_act p \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: set_thread_state_act_def)

lemma sts_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> set_thread_state t ts \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: set_thread_state_def wp: set_object_wp)

lemma update_sk_obj_ref_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> update_sk_obj_ref C f p v \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def partial_inv_def the_equality
       wp: set_object_wp get_object_wp get_simple_ko_wp)

lemma update_sched_context_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> update_sched_context p v \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: update_sched_context_def wp: set_object_wp get_object_wp)

lemma reply_unlink_tcb_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> reply_unlink_tcb t r \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def set_simple_ko_def wp: hoare_drop_imp set_object_wp)

lemma reply_unlink_sc_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> reply_unlink_sc sc r \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: reply_unlink_sc_def set_simple_ko_def
      wp: hoare_drop_imp set_object_wp)

lemma sched_context_donate_cdt_cdt_list[wp]:
  "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> sched_context_donate sc r \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  supply if_cong[cong]
  by (wpsimp simp: sched_context_donate_def set_tcb_obj_ref_def
       wp: set_object_wp hoare_drop_imp)

lemma reply_remove_cdt_cdt_list[wp]:
   "\<lbrace>\<lambda>s. P (cdt s) (cdt_list s)\<rbrace> reply_remove t r \<lbrace>\<lambda>_ s. P (cdt s) (cdt_list s)\<rbrace>"
  by (wpsimp simp: reply_remove_def
       wp: hoare_drop_imps hoare_vcg_all_lift)

lemma possible_switch_to_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> possible_switch_to r \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: possible_switch_to_def)

lemma set_mrs_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> set_mrs ptr buf msgs \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: set_mrs_def zipWithM_x_mapM_x split_del: if_split
        wp: hoare_drop_imp set_object_wp hoare_vcg_if_lift2 mapM_x_wp')

crunches
  cancel_all_signals, unbind_maybe_notification, sched_context_unbind_all_tcbs,
  sched_context_unbind_ntfn, sched_context_maybe_unbind_ntfn,
  sched_context_unbind_yield_from, cancel_all_ipc, thread_set, reply_remove_tcb
  for valid_list[wp]: valid_list
  (wp: mapM_x_wp' hoare_drop_imp)

crunch all_but_exst[wp]: update_work_units "all_but_exst P"

crunch all_but_exst[wp]: reset_work_units "all_but_exst P"

global_interpretation update_work_units_ext_extended: is_extended "update_work_units"
  by (unfold_locales; wp)

global_interpretation reset_work_units_ext_extended: is_extended "reset_work_units"
  by (unfold_locales; wp)

lemma preemption_point_inv':
  "\<lbrakk>irq_state_independent_A P; time_state_independent_A P; getCurrentTime_independent_A P;
    update_time_stamp_independent_A P; cur_time_independent_A P;
    \<And>f s. P (work_units_completed_update f s) = P s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> preemption_point \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: preemption_point_def)
  apply (rule validE_valid)
  apply (rule hoare_seq_ext_skipE, wpsimp simp: update_work_units_def)
  apply (rule valid_validE)
  apply (rule OR_choiceE_weak_wp)
  apply (rule alternative_valid; (solves wpsimp)?)
  apply (rule validE_valid)
  apply (rule hoare_seq_ext_skipE, (solves \<open>wpsimp simp: reset_work_units_def\<close>)?)+
  apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imps update_time_stamp_wp)
  done

locale Deterministic_AI_1 =
  assumes cap_swap_for_delete_valid_list[wp]:
    "\<And>param_a param_b. \<lbrace>valid_list\<rbrace> cap_swap_for_delete param_a param_b \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes finalise_cap_valid_list:
    "\<And>param_a param_b. \<lbrace>valid_list\<rbrace> finalise_cap param_a param_b \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes get_cap_valid_list[wp]:
    "\<And>param_a. \<lbrace>valid_list\<rbrace> get_cap param_a \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes arch_get_sanitise_register_info_valid_list[wp]:
    "\<And>t. \<lbrace>valid_list\<rbrace> arch_get_sanitise_register_info t \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes arch_post_modify_registers_valid_list[wp]:
    "\<And>t ptr. \<lbrace>valid_list\<rbrace> arch_post_modify_registers t ptr \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes make_arch_fault_msg_valid_list[wp]:
    "\<And>afault thread. \<lbrace>valid_list\<rbrace> make_arch_fault_msg afault thread \<lbrace>\<lambda>_. valid_list\<rbrace>"
  notes if_cong[cong]

context Deterministic_AI_1 begin

lemmas rec_del_valid_list[wp] = rec_del_preservation
  [OF cap_swap_for_delete_valid_list
      set_cap_valid_list
      empty_slot_valid_list
      finalise_cap_valid_list]

crunch valid_list[wp]: cap_delete valid_list
  (wp: preemption_point_inv')

end

lemma irq_state_independent_A_valid_list[simp]: "irq_state_independent_A valid_list"
  by (simp add: irq_state_independent_A_def)

context Deterministic_AI_1 begin

lemma cap_revoke_valid_list[wp]:"\<lbrace>valid_list\<rbrace> cap_revoke a \<lbrace>\<lambda>_. valid_list\<rbrace>"
  apply (rule cap_revoke_preservation2)
  apply (wp preemption_point_inv'|simp)+
  done

end

lemma cancel_badged_sends_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> cancel_badged_sends a b \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: cancel_badged_sends_def wp: filterM_preserved hoare_drop_imp)

context Deterministic_AI_1 begin

lemma invoke_cnode_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> invoke_cnode ci \<lbrace>\<lambda>_.valid_list\<rbrace>"
  apply (rule hoare_pre)
   apply (wp crunch_wps cap_move_src_slot_Null hoare_drop_imps hoare_vcg_all_lift | wpc | simp add: invoke_cnode_def crunch_simps split del: if_split)+
  done

end

lemma (in Deterministic_AI_1) set_priority_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> set_priority a b \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: set_priority_def reorder_ntfn_def reorder_ep_def thread_set_priority_def thread_set_def
               wp: get_simple_ko_wp hoare_drop_imp hoare_vcg_all_lift)

lemma set_mcpriority_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> set_mcpriority a b \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: set_mcpriority_def)

crunch (empty_fail)empty_fail[wp]: set_priority,set_mcpriority

lemma reply_push_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>_. valid_list\<rbrace>"
  by (wpsimp simp: reply_push_def bind_sc_reply_def
    wp: get_simple_ko_wp hoare_drop_imp get_sched_context_wp hoare_vcg_all_lift hoare_vcg_if_lift2)

lemma copy_mrs_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> copy_mrs sender sbuf receiver rbuf n \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: copy_mrs_def split_del: if_split
       wp: mapM_wp')

context Deterministic_AI_1 begin

crunch valid_list[wp]: make_fault_msg valid_list
  (ignore: make_arch_fault_msg)

crunch valid_list[wp]: do_fault_transfer valid_list
  (wp: mapM_wp hoare_drop_imp ignore: make_fault_msg)

crunch valid_list[wp]: transfer_caps,do_normal_transfer,do_ipc_transfer,refill_unblock_check valid_list
  (wp: mapM_wp hoare_drop_imp whileLoop_wp')

lemma send_ipc_valid_list[wp]:
  "send_ipc block call badge can_grant can_reply_grant can_donate thread epptr \<lbrace>valid_list\<rbrace>"
   by (wpsimp simp: send_ipc_def wp: thread_get_inv hoare_drop_imp get_simple_ko_wp)

crunch valid_list[wp]: send_fault_ipc,handle_timeout valid_list

end

crunch (empty_fail) empty_fail[wp]: tcb_release_enqueue

crunch valid_list[wp]: tcb_release_enqueue "valid_list"
  (simp: thread_get_def crunch_simps wp: get_object_wp mapM_wp hoare_drop_imp ignore: )

lemma postpone_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> postpone r \<lbrace>\<lambda>_.valid_list\<rbrace>"
   by (wpsimp simp: postpone_def wp: hoare_drop_imp)

crunches set_refills,refill_size
  for valid_list[wp]: valid_list

lemma refill_budget_check_valid_list[wp]:
  "refill_budget_check usage \<lbrace>valid_list\<rbrace>"
  unfolding refill_budget_check_defs
  apply (wpsimp wp: whileLoop_wp' hoare_drop_imps)
  done

lemma refill_budget_check_round_robin_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> refill_budget_check_round_robin usage \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding refill_budget_check_round_robin_def update_refill_tl_def update_refill_hd_def
  by (wpsimp wp: hoare_drop_imps)

crunch valid_list[wp]: update_restart_pc "valid_list"

context Deterministic_AI_1 begin

lemma end_timeslice_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>_.valid_list\<rbrace>"
   by (wpsimp simp: end_timeslice_def wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma charge_budget_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> charge_budget consumed canTimeout \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: charge_budget_def Let_def set_refills_def is_round_robin_def
                   refill_budget_check_round_robin_def refill_reset_rr_def update_refill_tl_def
                   update_refill_hd_def set_refill_tl_def set_refill_hd_def
               wp: assert_inv
      | intro conjI)+

lemma check_budget_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> check_budget \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: check_budget_def)

crunch valid_list[wp]: check_budget_restart "valid_list"
  (simp: thread_get_def wp: hoare_drop_imp)

crunch valid_list[wp]: handle_fault "valid_list"
  (simp: thread_get_def unless_def wp: get_object_wp)

end

crunch valid_list[wp]: tcb_release_enqueue "valid_list"
  (simp: thread_get_def wp: get_object_wp mapM_wp hoare_drop_imp ignore: )

crunch (empty_fail) empty_fail[wp]: test_possible_switch_to

lemma test_possible_switch_to_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> test_possible_switch_to t \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: test_possible_switch_to_def)

lemma sched_context_resume_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> sched_context_resume sc_opt \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: sched_context_resume_def get_tcb_queue_def thread_get_def
          wp: get_sched_context_wp hoare_drop_imp hoare_vcg_if_lift2)

crunch valid_list[wp]: blocked_cancel_ipc,cancel_signal "valid_list"
  (wp: crunch_wps)

lemma cancel_ipc_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> cancel_ipc tp \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (wpsimp simp: cancel_ipc_def
      wp: hoare_drop_imp get_sched_context_wp hoare_vcg_conj_lift hoare_vcg_all_lift)

crunch valid_list[wp]: sched_context_unbind_reply valid_list

lemma fast_finalise_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> fast_finalise c b \<lbrace>\<lambda>_. valid_list\<rbrace>"
  by (cases c; wpsimp wp: gts_wp get_simple_ko_wp)

crunches cap_delete_one, restart
  for valid_list[wp]: "valid_list"
  (wp: hoare_drop_imp hoare_vcg_all_lift maybeM_inv simp: crunch_simps)

context notes if_cong[cong] begin

crunch valid_list[wp]: update_time_stamp "valid_list"
  (wp: get_object_wp)

crunch valid_list[wp]: reply_from_kernel "valid_list"
  (wp: get_object_wp)

crunch valid_list[wp]: sched_context_resume,suspend "valid_list"
  (wp: get_object_wp hoare_drop_imp maybeM_inv)

crunch valid_list[wp]: sched_context_bind_ntfn valid_list
crunch valid_list[wp]: sched_context_yield_to valid_list
  (wp: hoare_drop_imps crunch_wps simp: crunch_simps)
crunch valid_list[wp]: invoke_sched_context valid_list

crunch valid_list[wp]: refill_update,refill_new valid_list (wp: hoare_drop_imp)


crunch valid_list[wp]: commit_time valid_list
  (wp: crunch_wps)

end

context Deterministic_AI_1 begin

crunch valid_list[wp]: invoke_tcb, invoke_sched_control_configure_flags "valid_list"
 (wp: hoare_drop_imp check_cap_inv mapM_x_wp')

end

lemma delete_objects_valid_list[wp]: "\<lbrace>valid_list\<rbrace> delete_objects ptr bits \<lbrace>\<lambda>_.valid_list\<rbrace>"
  unfolding delete_objects_def
  apply (wp | simp add: detype_def)+
  done

lemmas mapM_x_def_bak = mapM_x_def[symmetric]

crunch valid_list[wp]: maybe_donate_sc valid_list (wp: maybeM_inv)

locale Deterministic_AI_2 = Deterministic_AI_1 +
  assumes arch_invoke_irq_handler_valid_list[wp]:
    "\<And>i. arch_invoke_irq_handler i \<lbrace>valid_list\<rbrace>"
  assumes handle_interrupt_valid_list[wp]:
    "\<And>irq. \<lbrace>valid_list\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_.valid_list\<rbrace>"
  assumes handle_call_valid_list[wp]:
    "\<lbrace>valid_list\<rbrace> handle_call \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes handle_recv_valid_list[wp]:
    "\<And>param_a can_reply. \<lbrace>valid_list\<rbrace> handle_recv param_a can_reply \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes handle_send_valid_list[wp]:
    "\<And>param_a. \<lbrace>valid_list\<rbrace> handle_send param_a \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes handle_vm_fault_valid_list[wp]:
    "\<And>thread fault. \<lbrace>valid_list\<rbrace> handle_vm_fault thread fault \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes handle_yield_valid_list[wp]:
    "\<lbrace>valid_list\<rbrace> handle_yield \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes handle_hypervisor_fault_valid_list[wp]:
    "\<And>thread fault. \<lbrace>valid_list\<rbrace> handle_hypervisor_fault thread fault \<lbrace>\<lambda>_. valid_list\<rbrace>"
  assumes handle_invocation_valid_list[wp]:
    "\<And>calling blocking can_donate first_phase cptr.
       \<lbrace>valid_list\<rbrace> handle_invocation calling blocking can_donate first_phase cptr \<lbrace>\<lambda>_. valid_list\<rbrace>"


context Deterministic_AI_2 begin

crunch valid_list[wp]: invoke_irq_handler valid_list

lemma handle_event_valid_list[wp]:
  "\<lbrace>valid_list\<rbrace> handle_event e \<lbrace>\<lambda>_.valid_list\<rbrace>"
  by (case_tac e; wpsimp simp: wp: hoare_drop_imps whenE_inv hoare_vcg_if_lift2)

end
(**)

(* Recovering cdt_list operations that only consider sane cases.
   This is to recover the current refinement proofs.*)

lemma (in mdb_move_abs') dest_empty_list:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "valid_list_2 t m \<Longrightarrow> t dest = []"
  apply (insert dest_desc)
  apply (subgoal_tac "set (t dest) = {}")
   apply simp
  apply (simp add: valid_list_2_def)
  done

lemma update_cdt_list_bind: "do y \<leftarrow> (update_cdt_list f); update_cdt_list f' od =
       update_cdt_list (\<lambda>s. f' (f s))"
  apply (simp add: bind_def update_cdt_list_def gets_def
                   return_def get_def set_cdt_list_def
                   put_def)
  done

lemma update_list_eq: "(f (cdt_list e)) = (f' (cdt_list e)) \<Longrightarrow>
        update_cdt_list f e = update_cdt_list f' e"
  apply (simp add: update_cdt_list_def gets_def
                   get_def set_cdt_list_def put_def
                   bind_def return_def)
  done

lemma (in mdb_move_abs') cap_move_ext_det_def2:
 notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
 "valid_list_2 (cdt_list e) m \<Longrightarrow> src_p = (m src) \<Longrightarrow> dest_p = (m dest) \<Longrightarrow>
       cap_move_ext src dest src_p dest_p e =
    (update_cdt_list (\<lambda>list. case (m src) of
      None \<Rightarrow> list (src := [], dest := list src) |
      Some p \<Rightarrow> list (p := list_replace (list p) src dest,
                      src := [], dest := list src))) e"
  apply (simp add: cap_move_ext_def update_cdt_list_bind)
  apply (rule update_list_eq)
  apply (insert dest_None neq)
  apply (case_tac "m src")
    apply (simp add: dest_empty_list)
   apply simp
  apply (insert no_mloop)
  apply (frule no_mloop_weaken[where a=src])
  apply simp
  apply (insert dest_desc)
  apply (intro impI conjI)
   apply (simp add: no_children_empty_desc[symmetric])
  apply (simp add: dest_empty_list)
  done

lemma (in mdb_insert_abs) cap_insert_ext_det_def2:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
 "valid_list_2 (cdt_list e) m \<Longrightarrow> no_mloop m \<Longrightarrow> src_p = (m src) \<Longrightarrow> dest_p = (m dest) \<Longrightarrow>
       cap_insert_ext src_parent src dest src_p dest_p e = (\<lambda> src_parent src_slot dest_slot src_p dest_p.
    update_cdt_list (\<lambda>list. case (m src_slot) of
      None \<Rightarrow> list (
        src_slot := if src_parent then [dest_slot] @ (list src_slot) else list src_slot) |
      Some p \<Rightarrow> list (
        src_slot := if src_parent then [dest_slot] @ (list src_slot) else list src_slot,
        p := if src_parent then list p else list_insert_after (list p) src_slot dest_slot))) src_parent src dest src_p dest_p e"
  supply if_cong[cong]
  apply (simp add: cap_insert_ext_def update_cdt_list_bind)
  apply (rule update_list_eq)
  apply (simp split del: if_split cong: option.case_cong)
  apply (insert dest neq)
  apply (case_tac "m src")
   apply simp+
  apply (frule no_mloop_weaken[where a=src])
  apply simp
  done


lemma (in mdb_empty_abs') empty_slot_ext_det_def2:
 notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
 "valid_list_2 (cdt_list e) m \<Longrightarrow> slot_p = (m slot) \<Longrightarrow>
       empty_slot_ext slot slot_p e = (
    update_cdt_list (\<lambda>list. case (m slot) of None \<Rightarrow> list (slot := []) |
      Some p \<Rightarrow> list (p := list_replace_list (list p) slot (list slot), slot := []))) e"
  supply if_cong[cong]
  apply (simp add: empty_slot_ext_def update_cdt_list_bind)
  apply (rule update_list_eq)
  apply (simp cong: option.case_cong)
  apply (case_tac "m slot")
   apply simp
  apply (cut_tac no_mloop_weaken[OF no_mloop, where a=slot])
  apply simp
  done


lemma (in mdb_insert_abs) create_cap_ext_det_def2:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
 "valid_list_2 (cdt_list e) m \<Longrightarrow> dest_p = (m dest) \<Longrightarrow>
       create_cap_ext untyped dest dest_p e = (
    update_cdt_list (\<lambda>list. list (untyped := [dest] @ list untyped))) e"
  apply (simp add: create_cap_ext_def update_cdt_list_bind)
  apply (rule update_list_eq)
  apply (insert dest neq)
  apply (case_tac "m src")
   apply simp+
  done

(* next_sib_2 will give the same result as next_sib, which can
   be used to define the cdt_list of a node. next_sib_2 is introduced
   as it is comparable to functions (mdb_next) in the Haskell spec
   for use in the projection. next_sib_2 traverses the tree until
   it finds a sibling, rather than directly using the cdt_list. *)

function (domintros) next_sib_2 where
  "next_sib_2 slot p s =
  (if slot \<in> descendants_of p (cdt s) then
    case next_slot slot (cdt_list s) (cdt s) of Some next \<Rightarrow>
      if cdt s next = Some p then
        Some next
      else next_sib_2 next p s
    | None \<Rightarrow> None
  else None)"
  by (auto | atomize)+

lemma next_sib_2_domintros:
  "(\<And>x. \<lbrakk>slot \<in> descendants_of p (cdt s);
      next_slot slot (cdt_list s) (cdt s) = Some x;  cdt s x \<noteq> Some p\<rbrakk>
    \<Longrightarrow> next_sib_2_dom (x, p, s))
      \<Longrightarrow> next_sib_2_dom (slot, p, s)"
  apply(rule accpI)
  apply(erule next_sib_2_rel.cases)
  apply(simp)
  done

definition next_slot_set :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cdt \<Rightarrow> cslot_ptr set" where
  "next_slot_set slot t m \<equiv> {next. (next, slot) \<in> {(next, p). next_slot p t m = Some next}\<^sup>+}"

definition next_sib_set :: "cslot_ptr \<Rightarrow> cdt_list \<Rightarrow> cdt \<Rightarrow> cslot_ptr set" where
  "next_sib_set slot t m \<equiv> {next. (next, slot) \<in> {(next, p). next_sib p t m = Some next}\<^sup>+}"

lemma next_sib_set_same_parent:
  "\<lbrakk>next \<in> next_sib_set slot t m; valid_list_2 t m\<rbrakk>
    \<Longrightarrow> \<exists>p. m slot = Some p \<and> m next = Some p"
  apply (simp add: next_sib_set_def)
  by (induct "next" slot rule: trancl.induct; fastforce dest: next_sib_same_parent)

lemma next_slot_setD:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next \<in> next_slot_set slot t m; valid_list_2 t m; no_mloop m; finite_depth m\<rbrakk>
    \<Longrightarrow> next \<in> descendants_of slot m \<or> next \<in> next_sib_set slot t m \<or>
  (\<exists>p q. (slot \<in> descendants_of p m \<or> p = slot) \<and> q \<in> next_sib_set p t m \<and> next \<in> descendants_of q m \<union> {q})"
  apply(subst(asm) next_slot_set_def)
  apply(simp)
  apply(induct "next" slot rule: trancl.induct)
   apply(simp add: next_slot_def split: if_split_asm)
    apply(simp add: next_child_def valid_list_2_def descendants_of_def cdt_parent_defs)
    apply(case_tac "t b", simp, fastforce)
   apply(drule(2) next_not_childD)
   apply(erule disjE)
    apply(fastforce simp: next_sib_set_def)
   apply(fastforce simp: next_sib_set_def)
  apply(simp)
  apply(erule disjE)
   apply(simp add: next_slot_def split: if_split_asm)
    apply(rule disjI1)
    apply(rule_tac b=b in descendants_trans)
     apply(simp)
    apply(fastforce dest: next_childD simp: descendants_of_def cdt_parent_defs)
   apply(drule(2) next_not_childD)
   apply(fastforce simp: next_sib_set_def)
  apply(erule disjE)
   apply(simp add: next_slot_def split: if_split_asm)
    apply(rule disjI1)
    apply(fastforce intro: child_descendant dest: next_childD next_sib_set_same_parent)
   apply(drule(2) next_not_childD)
   apply(erule disjE, rule disjI2, rule disjI1)
    apply(fastforce simp: next_sib_set_def intro: trancl_into_trancl)
   apply(intro disjI2, elim exE conjE)
   apply(rule_tac x=q in exI)
   apply(fastforce simp: next_sib_set_def intro: trancl_into_trancl)
  apply(simp add: next_slot_def split: if_split_asm)
   apply(erule disjE)
    apply(rule disjI2)+
    apply(rule_tac x=p in exI)
    apply(rule conjI)
     apply(simp add: descendants_of_def cdt_parent_defs)
     apply(drule(1) next_childD)
     apply(drule_tac x=p in tranclD2)
     apply(elim exE conjE, simp)
     apply(fastforce dest: rtranclD)
    apply(fastforce)
   apply(rule disjI1)
   apply(frule(1) next_sib_set_same_parent)
   apply(drule(1) next_childD)
   apply(fastforce simp: descendants_of_def cdt_parent_defs intro: trancl_into_trancl2)
  apply(drule(2) next_not_childD)
  apply(rule disjI2)+
  apply(case_tac "next_sib c t m = Some b")
   apply(erule disjE)
    apply(simp)
    apply(rule_tac x=p in exI)
    apply(fastforce dest: next_sib_share_parent)
   apply(rule_tac x=c in exI)
   apply(simp)
   apply(rule_tac x=q in exI)
   apply(fastforce simp: next_sib_set_def intro: trancl_into_trancl)
  apply(simp | elim conjE exE)+
  apply(erule disjE)
   apply(rule_tac x=p in exI)
   apply(rule conjI)
    apply(rule disjI1)
    apply(drule_tac c=p in next_sib_share_parent, simp)
    apply(rule_tac b=qa in descendants_trans, simp, simp)
   apply(fastforce)
  apply(fastforce simp: next_sib_set_def intro: trancl_into_trancl)
  done

lemma list_eq_after_in_list:
  "\<lbrakk>valid_list_2 t m; m x = Some p\<rbrakk>
    \<Longrightarrow> \<exists>list. t p = list @ x # after_in_list_list (t p) x"
  apply(simp only:valid_list_2_def)
  apply (erule conjE)
  apply (drule_tac x = p in spec)+
  apply (subgoal_tac "x \<in> set (t p)")
   apply (drule_tac in_set_conv_nth[THEN iffD1], erule exE)
   apply (auto simp: in_set_conv_nth list_eq_after_in_list')
  done

lemma next_sib_set_eq_after_in_list_set_Some:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list_2 t m; m x = Some p\<rbrakk>
    \<Longrightarrow> next_sib_set x t m = {a. (a, x) \<in> {(next, c). after_in_list (t p) c = Some next}\<^sup>+}"
  apply(intro equalityI subsetI)
   apply(simp add: next_sib_set_def)
   apply(drule trancl_Collect_rev)
   apply(rule trancl_Collect_rev)
   apply(erule trancl_induct)
    apply(fastforce simp: next_sib_def split: option.splits)
   apply(rule trancl_into_trancl)
    apply(simp)
   apply(subgoal_tac "y \<in> next_sib_set x t m") (* bad *)
    prefer 2
    apply(fastforce simp: next_sib_set_def intro: trancl_Collect_rev)
   apply(fastforce simp: next_sib_def split: option.splits dest: next_sib_set_same_parent)
  apply(simp)
  apply(drule trancl_Collect_rev)
  apply(erule trancl_induct)
   apply(fastforce simp: next_sib_set_def next_sib_def split: option.splits)
  apply(simp add: next_sib_set_def)
  apply(subgoal_tac "y \<in> next_sib_set x t m")
   prefer 2
   apply(fastforce simp: next_sib_set_def intro: trancl_Collect_rev)
  apply(drule(1) next_sib_set_same_parent)
  apply(rule trancl_into_trancl2)
   apply(fastforce simp: next_sib_def split: option.splits)
  apply(simp)
  done

lemma next_sib_set_eq_after_in_list_set:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "valid_list_2 t m \<Longrightarrow> next_sib_set x t m = (case m x of None \<Rightarrow> {}
    | Some q \<Rightarrow> {a. (a, x) \<in> {(next, p). after_in_list (t q) p = Some next}\<^sup>+})"
  apply(simp add: next_sib_set_eq_after_in_list_set_Some split: option.splits)
  apply(fastforce simp: next_sib_set_def next_sib_def split: option.splits dest: tranclD2)
  done


lemma valid_list_distinct:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list_2 t m; m x = Some p\<rbrakk> \<Longrightarrow> distinct (t p)"
by (simp add:valid_list_2_def)

lemma next_sib_set_not_self:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "valid_list_2 t m \<Longrightarrow> x \<notin> next_sib_set x t m"
  apply(simp add: next_sib_set_eq_after_in_list_set valid_list_distinct after_in_list_list_set[symmetric] split: option.splits)
  apply(intro allI impI)
  apply(frule_tac p="the (m x)" in list_eq_after_in_list)
   apply(simp)
  apply(clarsimp simp add: valid_list_2_def)
  apply(erule_tac x="the (m x)" in allE)+
  apply(drule_tac x="t x" and f=distinct for x in arg_cong)
  apply(simp)
done

lemma next_slot_set_after_in_list:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next \<in> next_slot_set slot t m; m slot = Some p; m next = Some p; valid_list_2 t m; no_mloop m; finite_depth m\<rbrakk>
    \<Longrightarrow> next \<in> next_sib_set slot t m"
  apply(drule(3) next_slot_setD)
  apply(elim disjE)
    apply(simp add: descendants_of_def cdt_parent_defs no_mloop_def)
    apply(drule tranclD2)
    apply(fastforce dest: trancl_into_trancl rtranclD)
   apply(simp)
  apply(elim exE conjE)
  apply(frule(1) next_sib_set_same_parent)
  apply(simp)
  apply(elim conjE exE disjE)
     apply(fastforce dest: sib_not_desc)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(drule tranclD2)+
    apply(elim exE conjE)
    apply(drule rtranclD)+
    apply(elim disjE)
       apply(simp add: next_sib_set_not_self)
      apply(simp)
      apply(drule_tac x=za and y=q in sib_not_desc)
        apply(assumption)+
      apply(simp add: descendants_of_def cdt_parent_defs)
     apply(simp)
     apply(drule_tac x=za and y=pa in sib_not_desc)
       apply(assumption)+
     apply(simp add: descendants_of_def cdt_parent_defs)
    apply(simp)
    apply(subgoal_tac "za \<in> descendants_of pa m \<and> za \<in> descendants_of q m")
     prefer 2
     apply(simp add: descendants_of_def cdt_parent_defs)
    apply(erule conjE, drule(1) descendants_linear)
     apply(fastforce simp: next_sib_set_not_self)
    apply(simp add: sib_not_desc)
   apply(simp)
  apply(simp add: sib_not_desc)
  done

lemma next_slot_no_loop:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list_2 t m; no_mloop m; finite_depth m\<rbrakk>
    \<Longrightarrow> x \<notin> next_slot_set x t m"
  apply(rule notI)
  apply(case_tac "m x")
   apply(drule(2) next_slot_setD, simp)
   apply(simp add: next_sib_set_not_self)
   apply(erule disjE)
    apply(simp add: no_mloop_def descendants_of_def)
   apply(elim exE conjE)
   apply(erule disjE)
    apply(fastforce simp: descendants_of_def cdt_parent_defs dest: tranclD2)
   apply(fastforce simp: next_sib_set_def next_sib_def split: option.splits dest: tranclD2)
  apply(drule next_slot_set_after_in_list)
       apply(assumption)+
  apply(simp add: next_sib_set_not_self)
  done

lemma wf_next_slot:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>valid_mdb s; valid_list s\<rbrakk>
    \<Longrightarrow> wf {(next, p). next_slot p (cdt_list s) (cdt s) = Some next}"
  apply(rule finite_acyclic_wf)
   apply(insert cte_wp_at_set_finite)[1]
   apply(rule_tac B="{p. cte_wp_at \<top> p s} \<times> {p. cte_wp_at \<top> p s}" in finite_subset)
    apply(fastforce dest: cte_at_next_slot cte_at_next_slot' simp: finite_depth)
   apply(fastforce intro: finite_cartesian_product)
  apply(rule acyclicI)
  apply(frule finite_depth)
  apply(rule allI)
  apply(drule next_slot_no_loop, simp add: valid_mdb_def, simp add: finite_depth)
  apply(fastforce simp: next_slot_set_def)
  done

lemma next_slot_induct:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows
  "\<lbrakk>\<And>x. next_slot x (cdt_list s) (cdt s) = None \<Longrightarrow> P x; \<And>x y. \<lbrakk>next_slot x (cdt_list s) (cdt s) = Some y; P y\<rbrakk> \<Longrightarrow> P x;
    valid_mdb s; valid_list s\<rbrakk>
    \<Longrightarrow> P slot"
  apply(induct_tac rule: wf_induct[where r="{(next, p). next_slot p (cdt_list s) (cdt s) = Some next}"])
   apply(simp add: wf_next_slot)
  apply(fastforce split: if_split_asm)
  done

lemma next_sib_2_termination:
  "\<lbrakk>valid_mdb s; valid_list s\<rbrakk> \<Longrightarrow> next_sib_2_dom (slot, p, s)"
  apply(induct_tac slot rule: next_slot_induct[where s=s])
     apply(fastforce intro: next_sib_2_domintros)+
  done

lemma next_sib_2_pinduct':
  "\<lbrakk>next_sib_2_dom (slot, p, s);
   \<And>slot.
      \<lbrakk>next_sib_2_dom (slot, p, s);
       \<And>a. \<lbrakk>slot \<in> descendants_of p (cdt s);
          next_slot slot (cdt_list s) (cdt s) = Some a; cdt s a \<noteq> Some p\<rbrakk> \<Longrightarrow> P a t m\<rbrakk>
      \<Longrightarrow> P slot t m\<rbrakk>
  \<Longrightarrow> P slot t m"
  apply(induct rule: next_sib_2.pinduct)
  apply(simp)
  done

lemma next_sib_2_pinduct:
  "\<lbrakk>\<And>slot. \<lbrakk>\<And>a. \<lbrakk>slot \<in> descendants_of p (cdt s);
          next_slot slot (cdt_list s) (cdt s) = Some a; cdt s a \<noteq> Some p\<rbrakk> \<Longrightarrow> P a\<rbrakk>
    \<Longrightarrow> P slot; valid_mdb s; valid_list s\<rbrakk>
      \<Longrightarrow> P slot"
  apply(rule_tac t=t and m=m in next_sib_2_pinduct')
   apply(rule next_sib_2_termination)
    apply(assumption)+
  apply(fastforce)
  done

lemma next_slot_set_in_desc:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next \<in> next_slot_set slot (cdt_list s) (cdt s); cdt s next = Some p;
    slot \<in> descendants_of p (cdt s); next_slot slot (cdt_list s) (cdt s) = Some a;
    valid_list s; valid_mdb s\<rbrakk>
    \<Longrightarrow> a \<in> descendants_of p (cdt s)"
  apply(frule finite_depth)
  apply(subgoal_tac "no_mloop (cdt s)")
   prefer 2
   apply(simp add: valid_mdb_def)
  apply(frule(1) next_slot_setD)
    apply(simp add: valid_mdb_def, simp+)
  apply(elim disjE)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(drule_tac x=slot in tranclD2)
    apply(simp)
    apply(drule(1) rtrancl_trancl_trancl)
    apply(simp add: no_mloop_def cdt_parent_defs)
   apply(frule(1) next_sib_set_same_parent)
   apply(simp add: next_slot_def split: if_split_asm)
    apply(drule(1) next_childD)
    apply(simp add: descendants_of_def cdt_parent_defs)
    apply(rule_tac b=slot in r_r_into_trancl)
     apply(simp)
    apply(simp)
   apply(simp add: next_not_child_termination)
   apply(simp split: if_split_asm option.splits)
    apply(fastforce dest: tranclD2 simp: next_sib_set_def)+
   apply(drule(1) next_sib_same_parent, simp add: child_descendant)
  apply(elim exE conjE)
  apply(subgoal_tac "q = next")
   prefer 2
   apply(subgoal_tac "pa \<in> descendants_of p (cdt s)")
    prefer 2
    apply(erule disjE)
     apply(frule_tac b=p and c=pa in descendants_linear, simp)
      apply(frule(1) next_sib_set_same_parent)
      apply(elim exE conjE)
      apply(rule notI, simp)
      apply(erule disjE)
       apply(simp add: no_mloop_weaken)
      apply(frule_tac a="next" and c=pa in descendants_linear)
        apply(simp add: child_descendant)
       apply(fastforce simp: next_sib_set_not_self)
      apply(simp add: sib_not_desc)
     apply(frule(1) next_sib_set_same_parent)
     apply(erule disjE)+
       apply(simp add: child_descendant)
      apply(simp)
     apply(erule disjE)
      apply(frule_tac a=p and c=q in descendants_linear)
        apply(simp add: descendants_of_def cdt_parent_defs)
        apply(drule_tac x=q in tranclD2)
        apply(simp)
        apply(drule rtranclD)
        apply(elim disjE exE conjE)
         apply(fastforce dest: sib_not_desc[simplified descendants_of_def cdt_parent_defs])
        apply(simp)
       apply(fastforce simp: next_sib_set_not_self)
      apply(fastforce dest: sib_not_desc)
     apply(simp)
    apply(simp)
   apply(erule_tac P="next = q" in disjE, simp)
   apply(simp add: descendants_of_def cdt_parent_defs)
   apply(drule_tac x=q in tranclD2)
   apply(simp)
   apply(drule_tac x=q and z=pa in rtrancl_trancl_trancl, simp)
   apply(fastforce dest: sib_not_desc[simplified descendants_of_def cdt_parent_defs]
               next_sib_set_same_parent)
  apply(simp)
  apply(simp add: next_slot_def split: if_split_asm)
   apply(drule(1) next_childD)
   apply(rule descendants_trans)
    apply(rule child_descendant)
    apply(simp)
   apply(simp)
  apply(drule(2) next_not_childD)
  apply(erule_tac P="next_sib slot (cdt_list s) (cdt s) = Some a" in disjE)
   apply(simp add: next_sib_share_parent)
  apply(elim exE conjE)
  apply(case_tac "qa=pa")
   apply(fastforce intro: child_descendant dest: next_sib_same_parent next_sib_set_same_parent)
  apply(erule disjE)
   apply(frule_tac a=slot and b=pa and c=qa in descendants_linear)
     apply(simp)+
   apply(erule disjE)
    apply(fastforce simp: next_sib_set_def dest: tranclD2)
   apply(drule_tac a=qa and c=p in descendants_trans)
    apply(fastforce dest: next_sib_set_same_parent simp: child_descendant)
   apply(fastforce dest: next_sib_share_parent)
  apply(simp)
  apply(fastforce simp: next_sib_set_def dest: tranclD2)
  done

declare next_sib_2.psimps[simp]

lemma next_sib_2_NoneD:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes "next_sib_2 slot p s = None" "slot \<in> descendants_of p (cdt s)" "valid_mdb s"
     "valid_list s" "q \<in> next_slot_set slot (cdt_list s) (cdt s)"
  shows "cdt s q \<noteq> Some p"
  apply(insert assms)
  apply(rule notI)
  apply(case_tac "next_slot slot (cdt_list s) (cdt s)")
   apply(fastforce simp: next_slot_set_def dest: tranclD2)
  apply(frule(5) next_slot_set_in_desc)
  apply(erule notE[rotated])
  apply(simp)
  apply(induct slot rule: next_sib_2_pinduct[where s=s and p=p])
    apply(simp)
    apply(atomize)
    apply(simp)
    apply(elim impCE)
      apply(fastforce simp: next_sib_2_termination)
     apply(simp add: next_slot_set_def)
     apply(drule tranclD2, simp)
     apply(drule rtranclD)
     apply(fastforce simp: next_sib_2_termination)
    apply(case_tac "next_slot a (cdt_list s) (cdt s)")
     apply(simp add: next_slot_set_def)
     apply(drule tranclD2, simp)
     apply(drule rtranclD)
     apply(erule disjE)
      apply(fastforce simp: next_sib_2_termination)
     apply(fastforce dest: tranclD2)
    apply(case_tac "q=a")
     apply(fastforce simp: next_sib_2_termination)
    apply(subgoal_tac "q \<in> next_slot_set a (cdt_list s) (cdt s)")
     prefer 2
     apply(simp add: next_slot_set_def)
     apply(drule tranclD2, simp)
     apply(drule rtranclD)
     apply(fastforce simp: next_sib_2_termination)
    apply(frule_tac slot=a in next_slot_set_in_desc) (* rename *)
         apply(simp_all)
    apply(simp)
    apply(erule exE)
    apply(case_tac "cdt s a = Some p")
     apply(fastforce simp: next_sib_2_termination)
    apply(rule_tac x=y in exI)
    apply(fastforce simp: next_sib_2_termination)
   apply(simp_all add: assms)
   done

definition last_child where
  "last_child slot t = (if t slot = [] then None else Some (last (t slot)))"

definition last_child_set where
  "last_child_set slot t = {p. (p, slot) \<in> {(next, c). last_child c t = Some next}\<^sup>+}"

function (domintros) last_last_child where
  "last_last_child slot t = (case last_child slot t of None \<Rightarrow> None
                          | Some child \<Rightarrow> (if last_child child t = None then Some child
                                     else last_last_child child t))"
  by auto


lemma last_childD:
  notes split_paired_All[simp del]
  shows "\<lbrakk>last_child slot t = Some child; valid_list_2 t m\<rbrakk>
    \<Longrightarrow> m child = Some slot \<and> next_sib child t m = None"
  apply(rule context_conjI)
   apply(fastforce simp: valid_list_2_def last_child_def split: if_split_asm)
  apply(rule next_sib_NoneI[where p=slot])
  apply(case_tac "t slot")
   apply(simp)
  apply(simp add: valid_list_2_def last_child_def split: if_split_asm)
  apply(erule_tac x=slot in allE)+
  apply(drule after_in_list_last_None)
  apply(simp)
  done


lemma last_child_set_in_desc:
  "\<lbrakk>valid_list_2 t m; c \<in> last_child_set p t\<rbrakk> \<Longrightarrow> c \<in> descendants_of p m"
  apply(simp add: last_child_set_def)
  apply(erule trancl_induct)
   apply(fastforce simp: child_descendant dest: last_childD)
  apply(simp)
  apply(drule(1) last_childD)
  apply(erule conjE)
  apply(drule child_descendant)
  apply(rule descendants_trans)
   apply(simp)+
  done

lemma last_child_no_loop:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_list_2 t m; no_mloop m\<rbrakk>
    \<Longrightarrow> x \<notin> last_child_set x t"
  apply(rule notI)
  apply(drule(1) last_child_set_in_desc)
  apply(simp add: no_mloop_descendants)
  done


lemma wf_last_child:
  "\<lbrakk>valid_mdb s; valid_list s\<rbrakk> \<Longrightarrow> wf {(next, p). last_child p (cdt_list s) = Some next}"
  apply(rule finite_acyclic_wf)
   apply(insert cte_wp_at_set_finite)[1]
   apply(rule_tac B="{p. cte_wp_at \<top> p s} \<times> {p. cte_wp_at \<top> p s}" in finite_subset)
    apply(fastforce dest: last_childD child_descendant descendants_of_cte_at
                         descendants_of_cte_at2)
   apply(fastforce intro: finite_cartesian_product)
  apply(rule acyclicI)
  apply(rule allI)
  apply(drule_tac x=x in last_child_no_loop, simp add: valid_mdb_def)
  apply(simp add: last_child_set_def)
  done

lemma last_child_induct:
  "\<lbrakk>\<And>x. last_child x (cdt_list s) = None \<Longrightarrow> P x; \<And>x y. \<lbrakk>last_child x (cdt_list s) = Some y; P y\<rbrakk> \<Longrightarrow> P x;
    valid_mdb s; valid_list s\<rbrakk>
    \<Longrightarrow> P slot"
  apply(induct_tac rule: wf_induct[where r="{(next, p). last_child p (cdt_list s) = Some next}"])
   apply(simp add: wf_last_child)
  apply(fastforce split: if_split_asm)
  done

lemma last_last_child_termination:
  "\<lbrakk>valid_mdb s; valid_list s\<rbrakk> \<Longrightarrow> last_last_child_dom (slot, (cdt_list s))"
  apply(induct_tac slot rule: last_child_induct[where s=s])
     apply(fastforce intro: last_last_child.domintros)+
  done

declare last_last_child.psimps[simp]

lemma last_child_NoneD:
  "\<lbrakk>last_child x t = None; valid_list_2 t m\<rbrakk> \<Longrightarrow> descendants_of x m = {}"
  by(simp add: last_child_def empty_list_empty_desc split: if_split_asm)

lemma last_last_child_NoneD:
  notes split_paired_Ex[simp del]
  assumes "last_last_child slot (cdt_list s) = None" "valid_list s" "valid_mdb s"
  shows "descendants_of slot (cdt s) = {}"
  apply(insert assms)
  apply(simp add: last_last_child_termination)
  apply(simp split: if_split_asm option.splits)
   apply(simp add:last_child_NoneD)
  apply(erule exE)
  apply(induct slot rule: last_child_induct[where s=s])
     apply(fastforce dest: last_child_NoneD)
    apply(simp)
    apply(case_tac "last_child ya (cdt_list s)")
     apply(simp add: last_last_child_termination)
    apply(atomize, simp)
    apply(erule impE)
     apply(simp add: last_last_child_termination)
    apply(drule_tac slot=y in last_childD, simp)
    apply(fastforce dest: child_descendant)
   using assms
   apply(simp+)
  done

lemma last_child_None_empty_desc:
  "\<lbrakk>last_child slot t = None; valid_list_2 t m\<rbrakk> \<Longrightarrow> descendants_of slot m = {}"
  by (simp add: last_child_def empty_list_empty_desc split: if_split_asm)

lemma last_last_child_empty_desc:
  assumes "last_last_child slot (cdt_list s) = Some child" "valid_mdb s" "valid_list s"
  shows "descendants_of child (cdt s) = {}"
  apply(insert assms)
  apply(induct slot rule: last_child_induct[where s=s])
     apply(simp add: last_last_child_termination)
    apply(case_tac "y=child")
     apply(simp add: last_last_child_termination last_child_None_empty_desc
              split: if_split_asm)
    apply(simp)
    apply(atomize, erule impE)
     apply(subst(asm) last_last_child.psimps)
      apply(simp add: last_last_child_termination)
     apply(simp split: option.splits if_split_asm)
    apply(simp)
   using assms
   apply(simp+)
   done

lemma last_last_child_next_sib:
  assumes "last_last_child slot (cdt_list s) = Some child" "valid_mdb s" "valid_list s"
  shows "next_sib child (cdt_list s) (cdt s) = None"
  apply(insert assms)
  apply(induct slot rule: last_child_induct[where s=s])
     apply(simp add: last_last_child_termination)
    apply(case_tac "y=child")
     apply(fastforce dest: last_childD)
    apply(simp)
    apply(atomize, erule impE)
     apply(subst(asm) last_last_child.psimps)
      apply(simp add: last_last_child_termination)
     apply(simp split: option.splits if_split_asm)
    apply(simp)
   using assms
   apply(simp+)
   done

lemma last_last_child_in_desc:
  assumes "last_last_child slot (cdt_list s) = Some child" "valid_mdb s" "valid_list s"
  shows "child \<in> descendants_of slot (cdt s)"
  apply(insert assms)
  apply(induct slot rule: last_child_induct[where s=s])
     apply(simp add: last_last_child_termination)
    apply(case_tac "y=child")
     apply(simp add: last_last_child_termination)
     apply(drule last_childD, simp)
     apply(fastforce dest: child_descendant intro: descendants_trans split: option.splits)
    apply(simp)
    apply(atomize, erule impE)
     apply(subst(asm) last_last_child.psimps)
      apply(simp add: last_last_child_termination)
     apply(simp split: option.splits if_split_asm)
    apply(drule last_childD, simp)
    apply(fastforce dest: child_descendant descendants_trans)
   using assms
   apply(simp+)
   done

lemma last_last_child_next_not_child:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes "last_last_child slot (cdt_list s) = Some child" "valid_mdb s" "valid_list s"
  shows "next_not_child child (cdt_list s) (cdt s) = next_not_child slot (cdt_list s) (cdt s)"
  apply(insert assms)
  apply(frule(2) last_last_child_empty_desc)
  apply(frule(2) last_last_child_next_sib)
  apply(frule(2) last_last_child_in_desc)
  apply(induct slot rule: last_child_induct[where s=s])
     apply(simp add: last_last_child_termination)
    apply(case_tac "y=child")
     apply(subst next_not_child.psimps)
      apply(simp add: next_not_child_termination finite_depth)
     apply(drule last_childD, simp,simp)
    apply(simp, atomize)
    apply(elim impE)
      apply(subst(asm) last_last_child.psimps)
       apply(simp add: last_last_child_termination)
      apply(simp split: option.splits if_split_asm)
     apply(subst(asm) last_last_child.psimps)
      apply(simp add: last_last_child_termination)
     apply(simp split: if_split_asm)
     apply(rule last_last_child_in_desc, simp+)
    apply(drule last_childD, simp)
    apply(simp add: next_not_child_termination finite_depth)
   using assms
   apply(simp+)
   done

lemma last_child_NoneI:
  "\<lbrakk>descendants_of slot m = {}; valid_list_2 t m\<rbrakk>
    \<Longrightarrow> last_child slot t = None"
  by (simp add: last_child_def empty_list_empty_desc)

lemma last_last_childI:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes "child \<in> last_child_set slot (cdt_list s)"
   "descendants_of child (cdt s) = {}" "valid_mdb s" "valid_list s"
  shows "last_last_child slot (cdt_list s) = Some child"
  apply(insert assms)
  apply(induct slot rule: last_child_induct[where s=s])
     apply(fastforce simp: last_child_set_def dest: tranclD2)
    apply(simp)
    apply(case_tac "y=child")
     apply(simp add: last_last_child_termination last_child_NoneI)
    apply(atomize)
    apply(erule impE)
     apply(fastforce simp: last_child_set_def dest: tranclD2 rtranclD)
    apply(simp add: last_last_child_termination split: option.splits)
   using assms
   apply(simp+)
   done

lemma desc_next_slot_desc_or_sib:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes "p \<in> descendants_of slot (cdt s)""valid_list s" "valid_mdb s"
  shows "(\<exists>q. next_slot p (cdt_list s) (cdt s) = Some q \<and>
    q \<in> descendants_of slot (cdt s))
      \<or> last_last_child slot (cdt_list s) = Some p
        \<and> next_not_child p (cdt_list s) (cdt s) = next_not_child slot (cdt_list s) (cdt s)"
  apply(insert assms)
  apply(case_tac "last_last_child slot (cdt_list s) = Some p")
   apply(frule(2) last_last_child_empty_desc)
   apply(frule(2) last_last_child_next_not_child)
   apply(rule disjI2)
   apply(simp add: next_slot_def empty_list_empty_desc split: if_split_asm)
  apply(rule disjI1)
  apply(case_tac "next_slot p (cdt_list s) (cdt s)")
   apply(simp)
   apply(erule notE)
   apply(rule last_last_childI)
      apply(simp add: next_slot_def split: if_split_asm)
       apply(drule next_child_NoneD)
       apply(simp add: empty_list_empty_desc )
      apply(simp add: empty_list_empty_desc)
      apply(drule next_not_child_NoneD, simp add: finite_depth)
      apply(erule conjE)
      apply(induct slot rule: last_child_induct[where s=s])
         apply(simp add: last_child_None_empty_desc)
        apply(case_tac "y=p")
         apply(fastforce simp: last_child_set_def)
        apply(simp)
        apply(atomize)
        apply(erule impE)
         apply(simp add: descendants_of_def cdt_parent_defs)
         apply(frule tranclD, simp)
         apply(elim exE conjE)
         apply(drule rtranclD)
         apply(erule_tac P="z=p" in disjE)
          apply(simp add: valid_list_2_def)
          apply(erule conjE)
          apply(erule_tac x=x in allE)+
          apply(simp add: next_sib_def)
          apply(drule after_in_list_last_None)
          apply(drule after_in_list_None_last, simp)
          apply(simp add: last_child_def split: if_split_asm)
         apply(erule_tac x=z and P="\<lambda>q. (q, p) \<in> {(p, c). cdt s c = Some p}\<^sup>+ \<longrightarrow>
            next_sib q (cdt_list s) (cdt s) = None" in allE)
         apply(erule impE)
          apply(simp)
         apply(simp add: next_sib_def valid_list_2_def)
         apply(erule conjE)
         apply(erule_tac x=x in allE)+
         apply(drule after_in_list_last_None)
         apply(drule after_in_list_None_last, simp)
         apply(simp add: last_child_def split: if_split_asm)
        apply(fastforce simp: last_child_set_def intro: trancl_into_trancl)
       using assms
       apply(simp_all add: empty_list_empty_desc)
   apply(simp add: next_slot_def empty_list_empty_desc next_child_def split: if_split_asm list.splits)
  apply(simp add: next_slot_def split: if_split_asm)
   apply(fastforce dest: next_childD child_descendant descendants_trans)
  apply(drule next_not_childD, simp add: finite_depth, simp add: valid_mdb_def)
  apply(erule disjE)
   apply(fastforce dest: next_sib_share_parent)
  apply(rule ccontr)
  apply(elim exE conjE)
  apply(erule notE)
  apply(rule last_last_childI)
     apply(induct slot rule: last_child_induct[where s=s])
        apply(simp add: last_child_None_empty_desc)
       apply(case_tac "y=p")
        apply(fastforce simp: last_child_set_def)
       apply(simp)
       apply(atomize)
       apply(erule_tac x=a in allE)
       apply(erule_tac x=q and P="\<lambda>q. p \<in> descendants_of y (cdt s) \<longrightarrow>
            a \<notin> descendants_of y (cdt s) \<longrightarrow>
            next_sib q (cdt_list s) (cdt s) = Some a \<longrightarrow>
            p \<in> descendants_of q (cdt s) \<longrightarrow>
            (\<forall>q'. q' \<in> descendants_of q (cdt s) \<and> p \<in> descendants_of q' (cdt s) \<longrightarrow>
                  next_sib q' (cdt_list s) (cdt s) = None) \<longrightarrow>
            p \<in> last_child_set y (cdt_list s)" in allE)
       apply(simp)
       apply(elim impE)
         apply(subgoal_tac "x \<in> descendants_of q (cdt s) \<union> {q}")
          prefer 2
          apply(rule ccontr)
          apply(erule notE)
          apply(simp)
          apply(drule_tac c=x in next_sib_share_parent, simp)
          apply(drule(1) descendants_linear, simp)
          apply(simp)
         apply(simp add: descendants_of_def cdt_parent_defs)
         apply(frule tranclD, simp)
         apply(elim exE conjE)
         apply(drule rtranclD)
         apply(erule_tac P="z=p" in disjE)
          apply(simp add: valid_list_2_def)
          apply(erule conjE)
          apply(erule_tac x=x in allE)+
          apply(simp add: next_sib_def)
          apply(drule after_in_list_last_None)
          apply(drule after_in_list_None_last, simp)
          apply(simp add: last_child_def split: if_split_asm)
         apply(erule_tac x=z in allE)
         apply(erule impE)
          apply(rule conjI)
           apply(fastforce intro: trancl_into_trancl)
          apply(fastforce dest: rtranclD)
         apply(simp add: next_sib_def valid_list_2_def)
         apply(erule conjE)
         apply(erule_tac x=x in allE)+
         apply(drule after_in_list_last_None)
         apply(drule after_in_list_None_last, simp)
         apply(simp add: last_child_def split: if_split_asm)
        apply(rule notI, erule notE)
        apply(drule(1) last_childD)
        apply(fastforce dest: child_descendant intro: descendants_trans)
       apply(fastforce simp: last_child_set_def intro: trancl_into_trancl)
      using assms
      apply(simp_all add: empty_list_empty_desc)
      done

lemma finite_descendants:
  "valid_mdb s \<Longrightarrow> finite (descendants_of slot (cdt s))"
  apply(rule_tac B="{p. cte_at p s}" in finite_subset)
   apply(rule subsetI)
   apply(simp add: descendants_of_cte_at)
  apply(simp add: cte_wp_at_set_finite)
  done

lemma next_slot_linear:
  "\<lbrakk>a \<in> next_slot_set c t m; b \<in> next_slot_set c t m; a \<noteq> b\<rbrakk>
    \<Longrightarrow> a \<in> next_slot_set b t m \<or> b \<in> next_slot_set a t m"
  apply(clarsimp)
  apply(simp add: next_slot_set_def)
  apply(induct a c rule: trancl.induct)
   apply(simp)
   apply(erule tranclE)
    apply(simp)
   apply(simp)
  apply(simp)
  apply(case_tac "ba=b")
   apply(simp)
  apply(subgoal_tac "(b, ba) \<in> {(next, p). next_slot p t m = Some next}\<^sup>+")
   apply(simp)
  apply(erule_tac a=b and b=c in tranclE)
   apply(simp)
  apply(simp)
  done

lemma next_sib_in_next_slot_set:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next_sib slot (cdt_list s) (cdt s) = Some next; valid_list s; valid_mdb s\<rbrakk>
    \<Longrightarrow> next \<in> next_slot_set slot (cdt_list s) (cdt s)"
  apply(subgoal_tac "finite (descendants_of slot (cdt s))")
   prefer 2
   apply(rule finite_subset[OF _ cte_wp_at_set_finite[where P="\<top>\<top>" and s=s]])
   apply(fastforce simp: descendants_of_cte_at)
  apply(frule finite_depth)
  apply(subgoal_tac "no_mloop (cdt s)")
   prefer 2
   apply(simp add: valid_mdb_def)
  apply(case_tac "descendants_of slot (cdt s) = {}")
   apply(fastforce simp: next_slot_set_def next_slot_def empty_list_empty_desc next_not_child_termination)
  apply(case_tac "last_last_child slot (cdt_list s)")
   apply(drule(2) last_last_child_NoneD, simp)
  apply(case_tac "a \<in> next_slot_set slot (cdt_list s) (cdt s)")
   apply(frule(2) last_last_child_empty_desc)
   apply(drule(2) last_last_child_next_not_child)
   apply(simp add: next_slot_set_def)
   apply(rule_tac b=a in trancl_into_trancl2)
    apply(simp add: next_slot_def empty_list_empty_desc next_not_child_termination)
   apply(simp)
  apply(subgoal_tac "next_slot_set slot (cdt_list s) (cdt s) \<subseteq> descendants_of slot (cdt s)")
   prefer 2
   apply(rule subsetI)
   apply(simp add: next_slot_set_def)
   apply(drule trancl_Collect_rev)
   apply(erule trancl_induct)
    apply(simp add: empty_list_empty_desc next_slot_def)
    apply(drule(1) next_childD, simp add: child_descendant)
   apply(simp)
   apply(drule(2) desc_next_slot_desc_or_sib)
   apply(erule disjE, simp)
   apply(drule_tac b=y in trancl_Collect_rev)
   apply(simp)
  apply(subgoal_tac "(\<lambda>p. the (next_slot p (cdt_list s) (cdt s))) ` (next_slot_set slot (cdt_list s) (cdt s)) \<subset> next_slot_set slot (cdt_list s) (cdt s)")
   prefer 2
   apply(simp add: image_def)
   apply(rule psubsetI)
    apply(rule subsetI)
    apply(simp)
    apply(erule bexE)
    apply(simp add: next_slot_set_def)
    apply(case_tac "next_slot xa (cdt_list s) (cdt s)")
     apply(drule_tac c=xa in subsetD)
      apply(simp)
     apply(drule(2) desc_next_slot_desc_or_sib, simp)
    apply(drule trancl_Collect_rev)
    apply(drule_tac c=x in trancl_into_trancl)
     apply(case_tac "next_slot xa (cdt_list s) (cdt s)")
      apply(simp)
     apply(simp add: the_def)
    apply(simp)
    apply(drule trancl_Collect_rev, simp)
   apply(case_tac "next_slot slot (cdt_list s) (cdt s)")
    apply(fastforce simp: next_slot_def empty_list_empty_desc next_child_def split: if_split_asm list.splits)
   apply(rule_tac x=aa in set_neqI[symmetric])
    apply(fastforce simp: next_slot_set_def)
   apply(rule ccontr, simp)
   apply(erule bexE)
   apply(simp)
   apply(subgoal_tac "\<exists>y. next_slot x (cdt_list s) (cdt s) = Some y")
    prefer 2
    apply(rule ccontr)
    apply(simp)
    apply(drule_tac c=x in subsetD)
     apply(simp)
    apply(drule(2) desc_next_slot_desc_or_sib, simp)
   apply(erule exE, simp)
   apply(frule_tac x=y in next_slot_no_loop, assumption+)
   apply(erule notE)+
   apply(simp add: next_slot_set_def)
   apply(drule tranclD2, simp)
   apply(drule rtranclD)
   apply(erule disjE, fastforce)
   apply(rule_tac b=x in trancl_into_trancl2)
    apply(simp)
   apply(simp)
  apply(frule finite_subset)
   apply(simp add: finite_descendants)
  apply(frule(1) psubset_card_mono)
  apply(drule_tac f="(\<lambda>p. the (next_slot p (cdt_list s) (cdt s)))" and A="next_slot_set slot (cdt_list s) (cdt s)" in inj_on_iff_eq_card)
  apply(erule iffE)
  apply(erule impE)
   apply(simp)
   apply(rule inj_onI)
   apply(frule_tac c=x in subsetD, simp)
   apply(frule_tac c=y in subsetD, simp)
   apply(case_tac "next_slot x (cdt_list s) (cdt s)")
    apply(drule(2) desc_next_slot_desc_or_sib)+
    apply(simp)
   apply(case_tac "next_slot y (cdt_list s) (cdt s)")
    apply(drule(2) desc_next_slot_desc_or_sib)+
    apply(simp)
   apply(simp)
   apply(rule ccontr)
   apply(drule(2) next_slot_linear)
   apply(erule disjE)
    apply(drule_tac x=x in next_slot_no_loop, assumption+)
    apply(simp add: next_slot_set_def)
    apply(drule_tac x=x in tranclD2, simp)
    apply(drule_tac x=x and z=x in rtrancl_trancl_trancl)
     apply(rule r_into_trancl, simp+)
   apply(drule_tac x=y in next_slot_no_loop, assumption+)
   apply(simp add: next_slot_set_def)
   apply(drule_tac x=y and y=x in tranclD2, simp)
   apply(drule_tac x=y and z=y in rtrancl_trancl_trancl)
    apply(rule r_into_trancl, simp+)
    done


lemma next_sib_2_None_next_sib:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next_sib_2 slot p s = None; valid_mdb s; valid_list s; cdt s slot = Some p\<rbrakk>
    \<Longrightarrow> next_sib slot (cdt_list s) (cdt s) = None"
  apply(rule ccontr, simp, erule exE)
  apply(frule(2) next_sib_in_next_slot_set)
  apply(frule child_descendant)
  apply(drule(4) next_sib_2_NoneD)
  apply(fastforce dest: next_sibD next_sib_same_parent)
  done

lemma next_sib_2_in_next_slot_set:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes "next_sib_2 slot p s = Some next" "valid_list s" "valid_mdb s"
  shows "next \<in> next_slot_set slot (cdt_list s) (cdt s)"
  using assms
  apply(induct rule: next_slot_induct[where s=s])
     apply(simp add: next_sib_2_termination split: if_splits)
    apply(simp add: next_sib_2_termination split: if_splits)
     apply(fastforce simp: next_slot_set_def intro: trancl_into_trancl)
    apply(fastforce simp: next_slot_set_def intro: trancl_into_trancl)
   apply(insert assms, simp+)
   done

lemma next_sib_2_sib':
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes "next_sib_2 slot p s = Some next" "cdt s slot \<noteq> Some p" "valid_list s" "valid_mdb s"
  shows "cdt s next = Some p"
  apply(insert assms)
  apply(induct slot rule: next_sib_2_pinduct[where s=s and p=p])
    apply(simp)
    apply(frule(2) next_sib_2_in_next_slot_set)
    apply(case_tac "next_slot slot (cdt_list s) (cdt s)")
     apply(fastforce simp: next_slot_set_def dest: tranclD2)
    apply(simp)
    apply(atomize)
    apply(erule_tac x=a in allE, simp)
    apply(case_tac "a=next")
     apply(simp add: next_sib_2_termination split: if_split_asm | erule impE)+
   apply(insert assms, simp+)
   done

lemma next_sib_2_sib:
  "\<lbrakk>next_sib_2 slot p s = Some next; valid_list s; valid_mdb s\<rbrakk>
    \<Longrightarrow> cdt s next = Some p"
  apply(case_tac "cdt s slot = Some p")
   apply(simp add: next_sib_2_termination split: if_split_asm)
   apply(simp split: option.splits if_split_asm)
   apply(fastforce intro: next_sib_2_sib')+
   done

lemma ex_imp:
  "\<lbrakk>\<forall>x. P x \<longrightarrow> Q x; \<exists>x. P x\<rbrakk> \<Longrightarrow> \<exists>x. Q x"
  by auto

lemma next_sib_2I:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes "cdt s next = Some p" "next \<in> next_slot_set slot (cdt_list s) (cdt s)"
    "\<forall>q. q \<in> next_slot_set slot (cdt_list s) (cdt s) \<and>
     next \<in> next_slot_set q (cdt_list s) (cdt s) \<longrightarrow> cdt s q \<noteq> Some p"
    "slot \<in> descendants_of p (cdt s)" "valid_mdb s" "valid_list s"
  shows "next_sib_2 slot p s = Some next"
  using assms
  apply(induct slot rule: next_sib_2_pinduct[where s=s and p=p])
    apply(simp)
    apply(case_tac "next_slot slot (cdt_list s) (cdt s)")
     apply(fastforce simp: next_slot_set_def dest: tranclD2)
    apply(atomize)
    apply(erule_tac x=a in allE)
    apply(simp)
    apply(case_tac "a=next")
     apply(simp add: next_sib_2_termination)
    apply(erule impE)
     apply(rule notI)
     apply(erule_tac x=a in allE)
     apply(erule impE)
      apply(rule conjI)
       apply(fastforce simp: next_slot_set_def)
      apply(fastforce dest: rtranclD tranclD2 simp: next_slot_set_def)
     apply(simp)
    apply(elim impE)
       apply(fastforce simp: next_slot_set_def dest: rtranclD tranclD2)
      apply(intro allI impI notI)
      apply(erule_tac x=q in allE)
      apply(erule impE)
       apply(fastforce intro: trancl_into_trancl simp: next_slot_set_def)
      apply(simp)
     apply(drule(5) next_slot_set_in_desc, simp)
    apply(simp add: next_sib_2_termination)
    apply(erule_tac x=a in allE, erule impE)
     apply(rule conjI)
      apply(fastforce simp: next_slot_set_def)
     apply(fastforce simp: next_slot_set_def dest: tranclD2 rtranclD)
    using assms
    apply(simp)+
    done

lemma between_next_sib_2_not_sib:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  assumes
  "next_sib_2 slot p s = Some next" "q \<in> next_slot_set slot (cdt_list s) (cdt s)"
  "next \<in> next_slot_set q (cdt_list s) (cdt s)" "valid_list s" "valid_mdb s"
  shows "cdt s q \<noteq> Some p"
  using assms
  apply(subgoal_tac "no_mloop (cdt s)")
   prefer 2
   apply(simp add: valid_mdb_def)
  apply(frule finite_depth)
  apply(rule notI)
  apply(case_tac "next_sib_2 slot p s = Some q")
   apply(simp add: next_slot_no_loop)
  apply(subgoal_tac "\<exists>q'. next_sib_2 slot p s = Some q' \<and>
                   q \<in> next_slot_set q' (cdt_list s) (cdt s)")
   prefer 2
   apply(rule_tac P="\<lambda>q'. cdt s q' = Some p \<and>
    q' \<in> next_slot_set slot (cdt_list s) (cdt s) \<and>
    (\<forall>q. q \<in> next_slot_set slot (cdt_list s) (cdt s) \<and>
    q' \<in> next_slot_set q (cdt_list s) (cdt s) \<longrightarrow> cdt s q \<noteq> Some p) \<and>
    q \<in> next_slot_set q' (cdt_list s) (cdt s)" in ex_imp)
    apply(simp)
    apply(intro allI impI)
    apply(elim conjE)
    apply(drule(2) next_sib_2I)
       apply(simp add: next_sib_2_termination split: if_split_asm)
      apply(simp)
     apply(simp)
    apply(simp)
   apply(simp)
   apply(induct slot rule: next_slot_induct[where s=s])
      apply(fastforce simp: next_slot_set_def dest: tranclD2)
     apply(simp)
     apply(case_tac "y=next")
      apply(simp add: next_slot_set_def)
      apply(drule_tac x=q in tranclD2)
      apply(simp)
      apply(drule(1) rtrancl_trancl_trancl)
      apply(drule(2) next_slot_no_loop[simplified next_slot_set_def, where x=q])
      apply(simp)
     apply(case_tac "y=q")
      apply(simp add: next_sib_2_termination split: if_split_asm)
     apply(atomize)
     apply(elim impE)
       apply(simp add: next_sib_2_termination split: if_split_asm)
      apply(fastforce simp: next_slot_set_def dest: rtranclD tranclD2)
     apply(elim exE conjE)
     apply(rule_tac x=xa in exI)
     apply(simp)
     apply(rule conjI)
      apply(simp add: next_slot_set_def)
      apply(rule trancl_into_trancl)
       apply(simp)+
     apply(intro allI impI)
     apply(erule_tac x=qa in allE)
     apply(simp)
     apply(case_tac "qa=y")
      apply(simp add: next_sib_2_termination split: if_split_asm)
     apply(simp add: next_slot_set_def)
     apply(erule conjE)
     apply(drule_tac x=qa and y=x in tranclD2, simp)
     apply(drule rtranclD, simp)
    using assms
    apply(simp_all add: next_slot_set_def)
  apply(drule(1) trancl_trans[where y="next"])
  apply(fastforce dest: next_slot_no_loop simp: next_slot_set_def)
  done

lemma next_sib_set_in_next_slot_set:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next \<in> next_sib_set slot (cdt_list s) (cdt s); valid_list s; valid_mdb s\<rbrakk>
    \<Longrightarrow> next \<in> next_slot_set slot (cdt_list s) (cdt s)"
  apply(simp add: next_sib_set_def)
  apply(induct "next" slot rule: trancl.induct)
   apply(simp add: next_sib_in_next_slot_set)
  apply(simp add: next_slot_set_def)
  apply(rule trancl_trans)
   apply(simp)
  apply(drule(2) next_sib_in_next_slot_set)
  apply(simp add: next_slot_set_def)
  done

lemma next_sib_2_eq_next_sib:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>next_sib_2 slot p s = Some next; valid_list s; valid_mdb s; cdt s slot = Some p\<rbrakk>
    \<Longrightarrow> next_sib slot (cdt_list s) (cdt s) = Some next"
  apply(frule finite_depth, subgoal_tac "no_mloop (cdt s)")
   prefer 2
   apply(simp add: valid_mdb_def)
  apply(frule(2) next_sib_2_in_next_slot_set)
  apply(frule(2) next_sib_2_sib)
  apply(frule(5) next_slot_set_after_in_list)
  apply(simp add: next_sib_set_def)
  apply(drule tranclD2)
  apply(elim exE conjE)
  apply(simp)
  apply(drule rtranclD)
  apply(erule disjE, simp)
  apply(frule_tac q=z in between_next_sib_2_not_sib)
      apply(rule next_sib_in_next_slot_set)
        apply(simp, simp, simp)
     apply(rule next_sib_set_in_next_slot_set)
       apply(fastforce simp: next_sib_set_def, simp, simp)
    apply(simp, simp)
  apply(fastforce dest: next_sib_same_parent)
  done

lemma next_sib_def2:
  notes split_paired_All[simp del] split_paired_Ex[simp del]
  shows "\<lbrakk>valid_mdb s; valid_list s; cdt s slot = Some p\<rbrakk>
    \<Longrightarrow> next_sib_2 slot p s = next_sib slot (cdt_list s) (cdt s)"
  apply(case_tac "next_sib_2 slot p s")
   apply(fastforce dest: next_sib_2_None_next_sib)
  apply(fastforce dest: next_sib_2_eq_next_sib)
  done

end
