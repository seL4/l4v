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
  "../invariant-abstract/KernelInit_AI"
begin

(* Axiomatisation of the rest of the initialisation code *)
axiomatization where
  init_refinement:
  "Init_H a b c d e f \<subseteq> lift_state_relation state_relation `` Init_A"

  (* NOTE: this assumption became necessary after removal of duplicate
           page table and page directory entries (for large pages and
           super sections) in abstract.
    FIXME: should we prove the existence of a Haskell state that
           satisfies invs' and vs_valid_duplicates'? *)
axiomatization where
  ckernel_init_valid_duplicates':
  "\<forall>((tc,s),x) \<in> (Init_H a b c d e f). vs_valid_duplicates' (ksPSpace s)"

axiomatization where
  ckernel_init_invs:
  "\<forall>((tc,s),x) \<in> (Init_H a b c d e f). invs' s"

axiomatization where
  ckernel_init_sch_norm:
  "((tc,s),x) \<in> Init_H a b c d e f \<Longrightarrow> ksSchedulerAction s = ResumeCurrentThread"

axiomatization where
  ckernel_init_ctr:
  "((tc,s),x) \<in> Init_H a b c d e f \<Longrightarrow> ct_running' s"

end
