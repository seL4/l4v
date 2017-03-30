(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Toplevel Refinement Statement for nondeterministic specification"

theory Refine_nondet_C (* FIXME: broken *)
imports
  Refine_C
  "../../invariant-abstract/BCorres2_AI"
begin

definition (in state_rel)
  cstate_to_AN :: "cstate \<Rightarrow> unit Structures_A.state"
  where
  "cstate_to_AN \<equiv> truncate_state \<circ> absKState \<circ> cstate_to_H \<circ> globals"
definition (in state_rel)
  "Fin_CN \<equiv> \<lambda>((tc,s),m,e). ((tc, cstate_to_AN s),m,e)"

lemma truncate_trans[simp]: "truncate_state (trans_state f s) = s"
  by (simp add: trans_state_def)

context kernel
begin

definition
  ADT_C' :: "(cstate global_state, unit observable, global_transition) data_type"
where
 "ADT_C' \<equiv> \<lparr> Init = Init_C', Fin = Fin_CN,
            Step = global_automaton do_user_op_C (kernel_call_C False) \<rparr>"

definition
  ADT_FP_C' :: "(cstate global_state, unit observable, global_transition) data_type"
where
 "ADT_FP_C' \<equiv> \<lparr> Init = Init_C', Fin = Fin_CN,
               Step = global_automaton do_user_op_C (kernel_call_C True) \<rparr>"

lemma refinement2_both_nondet:
  "\<lparr> Init = Init_C', Fin = Fin_CN,
     Step = global_automaton do_user_op_C (kernel_call_C fp) \<rparr>
   \<sqsubseteq> ADT_H'"
  apply (cut_tac refinement2_both)
  apply (clarsimp simp add: refines_def execution_def ADT_H'_def ADT_H_def)
  apply (clarsimp simp add: Fin_CN_def cstate_to_AN_def Fin_C_def cstate_to_A_def Init_C_def)
  apply (rename_tac js aa ba aaa baa ad bd ae be)
  apply (drule_tac x=js in spec)
  apply (drule_tac x=aa in spec)
  apply (drule_tac x="trans_state (\<lambda>s. undefined) ba" in spec)
  apply (drule_tac x=aaa in spec)
  apply (drule_tac x=baa in spec)
  apply simp
  apply force
  done

theorem refinement2_nondet:
  "ADT_C' \<sqsubseteq> ADT_H'"
  unfolding ADT_C'_def
  by (rule refinement2_both_nondet)

theorem fp_refinement_nondet:
  "ADT_FP_C' \<sqsubseteq> ADT_H'"
  unfolding ADT_FP_C'_def
  by (rule refinement2_both_nondet)

theorem seL4_refinement_nondet:
  "ADT_C' \<sqsubseteq> ADT_A'"
  by (blast intro: refinement_nondet refinement2_nondet refinement_trans)

theorem seL4_fastpath_refinement_nondet:
  "ADT_FP_C' \<sqsubseteq> ADT_A'"
  by (blast intro: refinement_nondet fp_refinement_nondet refinement_trans)

end
