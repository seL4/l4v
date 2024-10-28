(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Dummy initial kernel state. Real kernel boot up is more complex.
*)

chapter "An Initial Kernel State"

theory Init_A
imports Retype_A
begin

context Arch begin arch_global_naming (A)

text \<open>
  This is not a specification of true kernel
  initialisation. This theory describes a dummy initial state only, to
  show that the invariants and refinement relation are consistent.
\<close>

(* Moved to Deterministic_A
definition
  idle_thread_ptr :: word32 where
  "idle_thread_ptr = kernel_base + 0x1000"
*)

definition
  init_tcb_ptr :: word32 where
  "init_tcb_ptr = kernel_base + 0x2000"

definition
  init_irq_node_ptr :: word32 where
  "init_irq_node_ptr = kernel_base + 0x8000"

definition
  init_globals_frame :: word32 where
  "init_globals_frame = kernel_base + 0x5000"

definition
  "us_global_pd_ptr = kernel_base + 0x60000"

definition
  "init_arch_state \<equiv> \<lparr>
    arm_asid_table = Map.empty,
    arm_hwasid_table = Map.empty,
    arm_next_asid = 0,
    arm_asid_map = Map.empty,
    arm_current_vcpu = None,
    arm_gicvcpu_numlistregs = undefined,
    arm_kernel_vspace = (\<lambda>ref.
      if ref \<in> {kernel_base .. kernel_base + mask 20}
      then ArmVSpaceKernelWindow
      else ArmVSpaceInvalidRegion),
    arm_us_global_pd = us_global_pd_ptr
  \<rparr>"

definition [simp]: "us_global_pd \<equiv> ArchObj (PageDirectory (\<lambda>_. InvalidPDE))"

definition
  "init_kheap \<equiv>
  (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
       then Some (CNode 0 (empty_cnode 0)) else None)
  (idle_thread_ptr \<mapsto> TCB \<lparr>
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
    tcb_arch = init_arch_tcb
  \<rparr>,
  us_global_pd_ptr \<mapsto> us_global_pd)"

definition
  "init_cdt \<equiv> Map.empty"

definition
  "init_ioc \<equiv>
   \<lambda>(a,b). (\<exists>obj. init_kheap a = Some obj \<and>
                  (\<exists>cap. cap_of obj b = Some cap \<and> cap \<noteq> cap.NullCap))"

definition
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
    interrupt_states = \<lambda>_. Structures_A.IRQInactive,
    arch_state = init_arch_state,
    exst = ext_init
  \<rparr>"

end


end
