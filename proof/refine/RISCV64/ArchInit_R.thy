(*
 * Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInit_R
imports
  Init_R
begin

context Arch begin arch_global_naming

clear_named_theorems Arch_assms (* accumulate assumptions for Init_R locale *)

definition zeroed_arch_abstract_state :: arch_state where
  "zeroed_arch_abstract_state \<equiv> \<lparr>
    riscv_asid_table    = Map.empty,
    riscv_global_pts    = K {},
    riscv_kernel_vspace = K RISCVVSpaceUserRegion\<rparr>"

definition zeroed_arch_intermediate_state :: Arch.kernel_state where
  "zeroed_arch_intermediate_state \<equiv> RISCVKernelState Map.empty (K []) (K RISCVVSpaceUserRegion)"

(* the None maps are a result of unfolding zeroed_main_abstract_state *)
lemma ghost_relation_wrapper_arch_intermediate_state[Arch_assms]:
  "ghost_relation_wrapper_2 (\<lambda>_. None) (\<lambda>_. None) (\<lambda>_. None) zeroed_arch_intermediate_state"
  unfolding ghost_relation_wrapper_def ghost_relation_def zeroed_arch_intermediate_state_def
  by simp

lemma non_empty_refine_arch_state_relation[Arch_assms]:
  "(zeroed_arch_abstract_state, zeroed_arch_intermediate_state) \<in> arch_state_relation Map.empty"
  unfolding zeroed_arch_abstract_state_def zeroed_arch_intermediate_state_def arch_state_relation_def
  by simp

lemmas Init_R_assms = Arch_assms (* extract accumulated assumptions *)

end (* Arch *)

interpretation Init_R?: Init_R RISCV64.zeroed_arch_abstract_state
                                RISCV64.zeroed_arch_intermediate_state
proof goal_cases
  case 1 show ?case by (intro_locales; (unfold_locales; (fact RISCV64.Init_R_assms)?)?)
qed

end
