(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Noninterference_Base_Refinement
imports Noninterference_Base
        Noninterference_Base_Alternatives
begin

(* we assume the same initial state for both systems *)
locale noninterference_refinement =
   abs?: complete_unwinding_system A s0 dom uwr policy out schedDomain +
   conc?: noninterference_system C s0 dom uwr policy out schedDomain
   for A :: "('a,'s,'e) data_type"
   and s0 :: "'s"
   and dom :: "'e \<Rightarrow> 's \<Rightarrow> 'd"
   and uwr :: "'d \<Rightarrow> ('s \<times> 's) set"
   and policy :: "('d \<times> 'd) set"
   and out :: "'d \<Rightarrow> 's \<Rightarrow> 'p"
   and schedDomain :: "'d"
   and C :: "('c,'s,'e) data_type" +
   assumes refines: "refines C A"

context noninterference_refinement begin

lemma reachable:
  "conc.reachable s \<Longrightarrow> abs.reachable s"
  apply(simp add: conc.reachable_def abs.reachable_def)
  using refines by (fastforce simp: refines_def)


lemma Step:
  "conc.Step a \<subseteq> abs.Step a"
  apply(simp add: conc.Step_def abs.Step_def)
  using refines by(fastforce simp: refines_def)

lemma confidentiality_u_refinement_closed:
  "abs.confidentiality_u \<Longrightarrow> conc.confidentiality_u"
  apply(simp add: abs.confidentiality_u_def)
  apply(subst conc.confidentiality_u_def)
  apply(blast intro: subsetD[OF Step] reachable)
  done

lemma confidentiality_u_weak_refinement_closed:
  "abs.confidentiality_u_weak \<Longrightarrow> conc.confidentiality_u_weak"
  apply(simp add: abs.confidentiality_u_weak_def)
  apply(subst conc.confidentiality_u_weak_def)
  apply(blast intro: subsetD[OF Step] reachable)
  done

lemma integrity_u_refinement_closed:
  "abs.integrity_u \<Longrightarrow> conc.integrity_u"
  apply(simp add: abs.integrity_u_def)
  apply(subst conc.integrity_u_def)
  apply(blast intro: subsetD[OF Step] reachable)
  done


lemma xources_subset:
  "abs.confidentiality_u \<Longrightarrow> abs.xources as s u \<subseteq> conc.xources as s u"
  apply(induct as arbitrary: s u)
   apply(simp add: abs.xources.xources_Nil conc.xources.xources_Nil)
  apply(simp add: abs.xources.xources_Cons conc.xources.xources_Cons)
  apply(rule conjI)
   apply(rule subsetI)
   apply(rule UnI1)
   apply(blast dest: subsetD[OF Step])
  apply(rule subsetI)
  apply(rule UnI2)
  apply(blast dest: subsetD[OF Step])
  done


lemma uwr_equiv:
  "abs.uwr_equiv s as t bs u \<Longrightarrow> conc.uwr_equiv s as t bs u"
  apply(insert refines)
  apply(fastforce simp: abs.uwr_equiv_def conc.uwr_equiv_def simp: refines_def dest: subsetD)
  done

lemma xNonleakage_gen_refinement_closed:
  "abs.xNonleakage_gen \<Longrightarrow> conc.xNonleakage_gen"
  apply(frule abs.xNonleakage_gen_confidentiality_u)
  apply(frule xources_subset)
  apply(clarsimp simp: abs.xNonleakage_gen_def conc.xNonleakage_gen_def)
  apply(drule (1) sameFor_subset_dom[OF _ xources_subset])
  apply(blast dest: reachable uwr_equiv)
  done

end


locale complete_noninterference_refinement = noninterference_refinement A s0 dom uwr policy out schedDomain C
   for A :: "('a,'s,'e) data_type"
   and s0 :: "'s"
   and dom :: "'e \<Rightarrow> 's \<Rightarrow> 'd"
   and uwr :: "'d \<Rightarrow> ('s \<times> 's) set"
   and policy :: "('d \<times> 'd) set"
   and out :: "'d \<Rightarrow> 's \<Rightarrow> 'p"
   and schedDomain :: "'d"
   and C :: "('c,'s,'e) data_type" +
   assumes Step_C: "Step_system C s0"

sublocale complete_noninterference_refinement \<subseteq> conc: complete_unwinding_system C s0 dom uwr policy out schedDomain
  apply(unfold_locales)
    using Step_C apply(fastforce simp: Step_system_def)
   using Step_C apply(fastforce simp: Step_system_def)
  apply(rule policy_refl)
  done

context complete_noninterference_refinement begin
lemma Noninfluence_strong_uwr_refinement_closed:
  "abs.Noninfluence_strong_uwr \<Longrightarrow>
    conc.Noninfluence_strong_uwr"
  apply(frule abs.Noninfluence_strong_uwr_confidentiality_u_weak)
  apply(drule abs.Noninfluence_strong_uwr_integrity_u)
  apply(drule confidentiality_u_weak_refinement_closed)
  apply(drule integrity_u_refinement_closed)
  apply(blast intro: conc.Noninfluence_strong_uwr)
  done

lemma Nonleakage_gen_refinement_closed:
  "abs.Nonleakage_gen \<Longrightarrow>
    conc.Nonleakage_gen"
  apply(simp add: abs.Nonleakage_gen_equiv_confidentiality_u conc.Nonleakage_gen_equiv_confidentiality_u)
  apply(erule confidentiality_u_refinement_closed)
  done

lemma Noninfluence_strong_quasi_refinement_closed:
  "\<lbrakk>abs.confidentiality_u_weak; abs.integrity_u;
        output_consistent\<rbrakk> \<Longrightarrow>
    conc.Noninfluence_strong"
  apply(rule conc.Noninfluence_strong)
    apply(erule confidentiality_u_weak_refinement_closed)
   apply assumption
  apply(erule integrity_u_refinement_closed)
  done

lemma Noninfluence_strong_uwr_quasi_refinement_closed:
  "\<lbrakk>abs.Noninfluence_strong_uwr;
        output_consistent\<rbrakk> \<Longrightarrow>
    conc.Noninfluence_strong"
  apply(rule conc.Noninfluence_strong)
    apply(rule confidentiality_u_weak_refinement_closed)
    apply(erule abs.Noninfluence_strong_uwr_confidentiality_u_weak)
   apply assumption
  apply(rule integrity_u_refinement_closed)
  apply(erule abs.Noninfluence_strong_uwr_integrity_u)
  done

end
end
