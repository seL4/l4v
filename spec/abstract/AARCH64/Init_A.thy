(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "An Initial Kernel State"

theory Init_A
imports
  Retype_A
  "Lib.SplitRule"
begin

context Arch begin arch_global_naming (A)

text \<open>
  This is not a specification of true kernel initialisation. This theory describes a dummy
  initial state only, to show that the invariants and refinement relation are consistent.
\<close>

(* Some address sufficiently aligned for one page *)
definition arm_global_pt_ptr :: obj_ref where
  "arm_global_pt_ptr = pptr_base + 0x2000"

(* Sufficiently aligned for irq type + cte_level_bits *)
definition init_irq_node_ptr :: obj_ref where
  "init_irq_node_ptr = pptr_base + 0xc000"

(* The highest user-virtual address that is still canonical.
   It can be larger than user_vtop, which is the highest address we allow to be mapped.
   For AArch64-hyp, user-virtual addresses are IPAs and since there is no sign extension,
   the value is the top of the entire IPA address space. *)
definition canonical_user :: "vspace_ref" where
  "canonical_user \<equiv> mask ipa_size"

(* This is not the layout the real kernel uses, but we are only trying to show that
   the invariants are consistent. These apply to the mappings of the (separate) kernel-level
   page table in hyp mode, not the user-level page tables, which have no kernel mappings. *)
definition init_vspace_uses :: "vspace_ref \<Rightarrow> arm_vspace_region_use" where
  "init_vspace_uses p \<equiv>
     if p \<in> {pptr_base ..< pptr_base + (1 << 30)} then ArmVSpaceKernelWindow
     else ArmVSpaceInvalidRegion"


definition init_arch_state :: arch_state where
  "init_arch_state \<equiv> \<lparr>
     arm_asid_table = Map.empty,
     arm_kernel_vspace = init_vspace_uses,
     arm_vmid_table = Map.empty,
     arm_next_vmid = 0,
     arm_us_global_vspace = arm_global_pt_ptr,
     arm_current_vcpu = None,
     arm_gicvcpu_numlistregs = undefined,
     arm_current_fpu_owner = None
   \<rparr>"


(* The user-level global table in hyp mode is entirely empty.
   Kernel-level mappings are in a separate kernel page table, which is not modeled here. *)
definition global_pt_obj :: arch_kernel_obj where
  "global_pt_obj \<equiv> PageTable (VSRootPT (\<lambda>_. InvalidPTE))"

definition init_kheap :: kheap where
  "init_kheap \<equiv>
    (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
           then Some (CNode 0 (empty_cnode 0))
           else None)
    (idle_thread_ptr \<mapsto>
       TCB \<lparr>
         tcb_ctable = NullCap,
         tcb_vtable = NullCap,
         tcb_reply = NullCap,
         tcb_caller = NullCap,
         tcb_ipcframe = NullCap,
         tcb_state = IdleThreadState,
         tcb_fault_handler = replicate word_bits False,
         tcb_ipc_buffer = 0,
         tcb_fault = None,
         tcb_bound_notification = None,
         tcb_mcpriority = minBound,
         tcb_priority = 0,
         tcb_time_slice = timeSlice,
         tcb_domain = default_domain,
         tcb_flags = {},
         tcb_arch = init_arch_tcb
         \<rparr>,
     arm_global_pt_ptr \<mapsto> ArchObj global_pt_obj
    )"

definition init_cdt :: cdt where
  "init_cdt \<equiv> Map.empty"

definition init_ioc :: "cslot_ptr \<Rightarrow> bool" where
  "init_ioc \<equiv>
     \<lambda>(a,b). (\<exists>obj. init_kheap a = Some obj \<and>
                    (\<exists>cap. cap_of obj b = Some cap \<and> cap \<noteq> cap.NullCap))"

definition init_A_st :: "'z::state_ext state"
  where
  "init_A_st \<equiv> \<lparr>
    kheap = init_kheap,
    cdt = init_cdt,
    is_original_cap = init_ioc,
    cur_thread = idle_thread_ptr,
    idle_thread = idle_thread_ptr,
    scheduler_action = resume_cur_thread,
    domain_list = [(0,15)],
    domain_index = 0,
    cur_domain = 0,
    domain_time = 15,
    ready_queues = const (const []),
    machine_state = init_machine_state,
    interrupt_irq_node = \<lambda>irq. init_irq_node_ptr + (ucast irq << cte_level_bits),
    interrupt_states = \<lambda>_. IRQInactive,
    arch_state = init_arch_state,
    exst = ext_init
  \<rparr>"

end
end
