(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* Kernel init refinement. Currently axiomatised.
*)

theory KernelInit_R
imports
  IncKernelInit
  "../../invariant-abstract/KernelInit_AI"
begin

(* Axiomatisation of the rest of the initialisation code *)
axiomatization where
  init_refinement:
  "Init_H \<subseteq> lift_state_relation state_relation `` Init_A"

axiomatization where
  ckernel_init_valid_duplicates':
  "\<forall>((tc,s),x) \<in> Init_H. vs_valid_duplicates' (ksPSpace s)"

axiomatization where
  ckernel_init_invs:
  "\<forall>((tc,s),x) \<in> Init_H. invs' s"

axiomatization where
  ckernel_init_sch_norm:
  "((tc,s),x) \<in> Init_H \<Longrightarrow> ksSchedulerAction s = ResumeCurrentThread"

axiomatization where
  ckernel_init_ctr:
  "((tc,s),x) \<in> Init_H \<Longrightarrow> ct_running' s"

axiomatization where
  ckernel_init_domain_time:
  "((tc,s),x) \<in> Init_H \<Longrightarrow> ksDomainTime s \<noteq> 0"

axiomatization where
  ckernel_init_domain_list:
  "((tc,s),x) \<in> Init_H \<Longrightarrow> length (ksDomSchedule s) > 0 \<and> (\<forall>(d,time) \<in> set (ksDomSchedule s). time > 0)"

end
