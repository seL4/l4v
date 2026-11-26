(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Kernel init refinement. Currently axiomatised.
*)

theory KernelInit_R
imports
  IncKernelInit
  "AInvs.KernelInit_AI"
begin

(* Axiomatisation of the rest of the initialisation code *)
axiomatization where
  init_refinement:
  "Init_H \<subseteq> lift_state_relation state_relation `` Init_A"

(* This axiom is only needed on architectures with page table duplicates (32-bit Arm).
   For other architectures, vs_valid_duplicates' is trivially True, making this axiom
   redundant but harmless.  *)
axiomatization where
  ckernel_init_valid_duplicates':
  "\<forall>((tc,s),x) \<in> Init_H. vs_valid_duplicates' (ksPSpace s)"

axiomatization where
  ckernel_init_invs:
  "\<forall>((tc,s),x) \<in> Init_H. invs' s"

lemma Init_H_state_relation:
  "((tc,s),x) \<in> Init_H \<Longrightarrow> (init_A_st, s) \<in> state_relation"
  using init_refinement
  by (fastforce simp: Init_A_def lift_state_relation_def)

lemma ckernel_init_sch_norm:
  "\<lbrakk> ((tc,s),x) \<in> Init_H;
     scheduler_action (init_A_st :: det_state) = resume_cur_thread \<rbrakk>
   \<Longrightarrow> ksSchedulerAction s = ResumeCurrentThread"
  by (fastforce dest: Init_H_state_relation simp: state_relation_def)

lemma ckernel_init_domain_time:
  "\<lbrakk> ((tc,s),x) \<in> Init_H; 0 < domain_time (init_A_st :: det_state) \<rbrakk>
   \<Longrightarrow> ksDomainTime s \<noteq> 0"
  by (fastforce dest: Init_H_state_relation simp: state_relation_def)

lemma ckernel_init_ct_idle:
  "((tc,s),x) \<in> Init_H \<Longrightarrow> ct_idle' s"
  apply (frule Init_H_state_relation)
  apply (drule bspec[OF ckernel_init_invs])
  apply (insert akernel_init_invs[where 'a=det_ext])
  apply (clarsimp simp: Init_A_def)
  apply (frule invs_valid_idle')
  apply (clarsimp simp: invs_def valid_state_def ct_in_state_def)
  apply (drule (1) only_idleD)
  apply (frule curthread_relation, frule state_relation_idle_thread)
  apply (clarsimp simp: ct_in_state'_def valid_idle'_def idle_tcb'_def pred_tcb_at'_def
                  elim!: obj_at'_weakenE)
  done

end
