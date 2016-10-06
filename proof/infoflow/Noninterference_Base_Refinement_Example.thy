(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Noninterference_Base_Refinement_Example
imports
  Noninterference_Base_Refinement
begin

(* I don't like the 'refinedby' definition above.
   the following example shows why.

   let the spec be:
   s0 \<rightarrow> s1 \<rightarrow> s1
      \<rightarrow> s2 \<rightarrow> s3 \<rightarrow> s3

   and let the implementation be:
   s0 \<rightarrow> s1 \<rightarrow> s3 \<rightarrow> s3
      \<rightarrow> s2 \<rightarrow> s3 \<rightarrow> s3

   Then the implementation can transition from s1 \<rightarrow> s3 but the
   spec cannot. But the implementation still refines the spec
   according to refinedby above. We prove this below.

   The 'refinedby' definition above seems to correspond to our
   top-level refinement statement on ADTs for seL4.

   TODO: - check whether our 'corres' can be derived from the
           forward simulation results for seL4.
*)

datatype state = S0 | S1 | S2 | S3

datatype event = OnlyEvent
definition Step  :: "event \<Rightarrow> (state \<times> state) set" where
  "Step \<equiv> (\<lambda> a. {(S0,S1), (S0,S2), (S1,S1), (S2,S3), (S3,S3)})"



definition Step' :: "event \<Rightarrow> (state \<times> state) set" where
  "Step' \<equiv> (\<lambda> a. {(S0,S1), (S0,S2), (S1,S3), (S2,S3), (S3,S3)})"



datatype domain = OnlyDom
definition dom :: "event \<Rightarrow> state \<Rightarrow> domain" where "dom \<equiv> \<lambda> x y. OnlyDom"

definition uwr :: "domain \<Rightarrow> (state \<times> state) set" where "uwr \<equiv> \<lambda> x. {(y,z). True}"

definition policy :: "(domain \<times> domain) set" where "policy \<equiv> {(OnlyDom,OnlyDom)}"

definition out :: "domain \<Rightarrow> state \<Rightarrow> state" where "out \<equiv> \<lambda> d x. x"

lemma execution_Step_0:
  "length as = 0 \<Longrightarrow> execution Step S0 as = {S0}"
  apply(clarsimp simp: execution_def)
  done

lemma execution_Step'_0:
  "length as = 0 \<Longrightarrow> execution Step' S0 as = {S0}"
  apply(clarsimp simp: execution_def)
  done

lemma length_nonzero:
  "length xs = Suc n \<Longrightarrow> \<exists> as a. xs = as @ [a] \<and> length as = n"
  apply(induct xs rule: rev_induct)
   apply simp
  apply simp
  done

lemma execution_Step_1:
  "length as = 1 \<Longrightarrow> execution Step S0 as = {S1,S2}"
  apply simp
  apply(drule length_nonzero)
  apply(clarify)
  apply(subst execution_append_one)
  apply(auto simp: execution_def Step_def)
  done

lemma execution_Step'_1:
  "length as = 1 \<Longrightarrow> execution Step' S0 as = {S1,S2}"
  apply simp
  apply(drule length_nonzero)
  apply(clarify)
  apply(subst execution_append_one)
  apply(auto simp: execution_def Step'_def)
  done


lemma execution_Step_2up:
  "\<lbrakk>length as = (Suc n); n \<ge> (Suc 0)\<rbrakk> \<Longrightarrow> execution Step S0 as = {S1,S3}"
  apply(induct n arbitrary: as)
   apply simp
  apply simp
  apply(case_tac "n=0")
   apply(frule length_nonzero)
   apply(clarify)
   apply(subst execution_append_one)
   apply clarsimp
   apply(rule equalityI)
    apply clarsimp
    apply(drule execution_Step_1[simplified])
    apply(fastforce simp: Step_def)
   apply (subst execution_Step_1, simp)
   apply (fastforce simp: Step_def)
  apply(frule length_nonzero)
  apply(clarify)
  apply(subst execution_append_one)
  apply clarsimp
  apply (fastforce simp: Step_def)
  done


lemma execution_Step'_2up:
  "\<lbrakk>length as = (Suc n); n \<ge> (Suc 0)\<rbrakk> \<Longrightarrow> execution Step' S0 as = {S3}"
  apply(induct n arbitrary: as)
   apply simp
  apply simp
  apply(case_tac "n=0")
   apply(frule length_nonzero)
   apply(clarify)
   apply(subst execution_append_one)
   apply clarsimp
   apply(rule equalityI)
    apply clarsimp
    apply(drule execution_Step'_1[simplified])
    apply(fastforce simp: Step'_def)
   apply (subst execution_Step'_1, simp)
   apply (fastforce simp: Step'_def)
  apply(frule length_nonzero)
  apply(clarify)
  apply(subst execution_append_one)
  apply clarsimp
  apply (fastforce simp: Step'_def)
  done


interpretation enabled_system_refinement Step S0 dom uwr policy out OnlyDom Step' S0
  apply(unfold_locales)
         apply(clarsimp)
         apply(case_tac s)
            apply(auto simp: Step_def uwr_def refl_on_def sym_def trans_def dom_def policy_def)[8]
    apply(case_tac d, simp_all add: policy_def)
  apply clarsimp
  apply(case_tac s, auto simp: Step'_def)
  done




lemma refinedby:
  "enabled_system_refinement.refinedby Step S0 Step'"
  apply(clarsimp simp: refinedby_def)
  apply(case_tac as)
   apply(subst (asm) execution_Step'_0, simp)
   apply(subst execution_Step_0, simp)
   apply assumption
  apply(case_tac "length list  = 0")
   apply(subst (asm) execution_Step'_1, simp)
   apply(subst execution_Step_1, simp)
   apply assumption
  apply(subst (asm) execution_Step'_2up, simp)
   apply(case_tac list, fastforce+)
  apply(subst execution_Step_2up, simp)
   apply(case_tac list, fastforce+)
  done

lemma not_corres:
  "\<not> enabled_system_refinement.corres Step S0 Step'"
  apply(clarsimp simp: corres_def)
  apply(rule_tac x="S1" in exI)
  apply(rule conjI)
   apply(simp add: reachable_def)
   apply(rule_tac x="[OnlyEvent]" in exI)
   apply(fastforce simp: Step'_def)
  apply(rule_tac x="OnlyEvent" in exI)
  apply(rule_tac x="S3" in exI)
  apply(fastforce simp: Step_def Step'_def)
  done


end
