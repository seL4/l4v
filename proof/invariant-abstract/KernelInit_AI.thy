(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Kernel init refinement. *)

theory KernelInit_AI
imports
  ArchKernelInit_AI
begin

(* FIXME arch-split: move ArchKernelInit_AI after this theory; set up proper interface *)
arch_requalify_facts ct_idle_init_A_st invs_A

lemma akernel_init_invs:
  "\<forall>((tc,s),m,e) \<in> Init_A. invs s \<and> ct_idle s"
  unfolding Init_A_def
  by (simp add: ct_idle_init_A_st invs_A)

end
