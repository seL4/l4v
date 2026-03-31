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

named_theorems Init_R_assms

definition zeroed_arch_abstract_state :: arch_state where
  "zeroed_arch_abstract_state \<equiv> \<lparr>
    x64_asid_table         = Map.empty,
    x64_global_pml4        = 0,
    x64_kernel_vspace      = K X64VSpaceUserRegion,
    x64_global_pts         = [],
    x64_global_pdpts       = [],
    x64_global_pds         = [],
    x64_current_cr3        = cr3 0 0 ,
    x64_allocated_io_ports = \<bottom>,
    x64_num_ioapics        = 0,
    x64_ioapic_nirqs       = K 0,
    x64_irq_state          = K IRQFree,
    x64_current_fpu_owner = None\<rparr>"

definition zeroed_arch_intermediate_state :: Arch.kernel_state where
  "zeroed_arch_intermediate_state \<equiv>
     X64KernelState Map.empty 0 [] [] [] (CR3 0 0)
                    (K X64VSpaceUserRegion) \<bottom> 0 (K 0) (K X64IRQFree) None"

(* the None maps are a result of unfolding zeroed_main_abstract_state *)
lemma ghost_relation_wrapper_arch_intermediate_state[Init_R_assms]:
  "ghost_relation_wrapper_2 (\<lambda>_. None) (\<lambda>_. None) (\<lambda>_. None) zeroed_arch_intermediate_state"
  unfolding ghost_relation_wrapper_def ghost_relation_def zeroed_arch_intermediate_state_def
  by simp

lemma non_empty_refine_arch_state_relation[Init_R_assms]:
  "(zeroed_arch_abstract_state, zeroed_arch_intermediate_state) \<in> arch_state_relation"
  unfolding zeroed_arch_abstract_state_def zeroed_arch_intermediate_state_def arch_state_relation_def
  by (simp add: cr3_relation_def x64_irq_relation_def comp_def)

end (* Arch *)

interpretation Init_R?: Init_R X64.zeroed_arch_abstract_state
                                X64.zeroed_arch_intermediate_state
proof goal_cases
  interpret Arch  .
  case 1 show ?case by (intro_locales; (unfold_locales; (fact Init_R_assms)?)?)
qed

end
