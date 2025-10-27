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

definition
  init_tcb_ptr :: word32 where
  "init_tcb_ptr = kernel_base + 0x2000"

definition
  init_irq_node_ptr :: word32 where
  "init_irq_node_ptr = kernel_base + 0x8000"

(* It is easy to remove a memory slot here, but once if we want to reserve other slots of memory, we have to do the proof of disjoint for example state again.
   Comment is left here so that next time we need 4k memory, we don't need to fix example state and can simply change its name. *)
definition
  init_globals_frame :: word32 where
  "init_globals_frame = kernel_base + 0x5000"

definition
  init_global_pd :: word32 where
  "init_global_pd = kernel_base + 0x60000"

definition
  "init_arch_state \<equiv> \<lparr>
    arm_asid_table = Map.empty,
    arm_hwasid_table = Map.empty,
    arm_next_asid = 0,
    arm_asid_map = Map.empty,
    arm_global_pd = init_global_pd,
    arm_global_pts = [],
    arm_kernel_vspace = \<lambda>ref.
      if ref \<in> {kernel_base .. kernel_base + mask 20}
      then ArmVSpaceKernelWindow
      else ArmVSpaceInvalidRegion
  \<rparr>"

definition
  [simp]:
  "global_pd \<equiv> (\<lambda>_. InvalidPDE)( ucast (kernel_base >> 20) := SectionPDE (addrFromPPtr kernel_base) {} 0 {})"

definition
  "init_kheap \<equiv>
  (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
       then Some (CNode 0 (empty_cnode 0)) else None)
  (idle_thread_ptr \<mapsto> TCB \<lparr>
    tcb_ctable = NullCap,
    tcb_vtable = NullCap,
    tcb_ipcframe = NullCap,
    tcb_fault_handler = NullCap,
    tcb_timeout_handler = NullCap,
    tcb_state = IdleThreadState,
    tcb_ipc_buffer = 0,
    tcb_fault = None,
    tcb_bound_notification = None,
    tcb_mcpriority = minBound,
    tcb_sched_context = Some idle_sc_ptr,
    tcb_yield_to = None,
    tcb_priority = 0,
    tcb_domain = default_domain,
    tcb_arch = init_arch_tcb
  \<rparr>,
  init_globals_frame \<mapsto> ArchObj (DataPage False ARMSmallPage), \<comment> \<open>FIXME: same reason as why we kept the definition of @{text init_globals_frame}\<close>
  init_global_pd \<mapsto> ArchObj (PageDirectory global_pd),
  idle_sc_ptr \<mapsto> SchedContext (default_sched_context
                                 \<lparr>sc_tcb := Some idle_thread_ptr,
                                  sc_refills := [\<lparr>r_time = 0, r_amount = MAX_PERIOD\<rparr>,
                                                 \<lparr>r_time = MAX_PERIOD, r_amount = 0\<rparr>],
                                  sc_budget := MAX_PERIOD,
                                  sc_refill_max := MIN_REFILLS\<rparr>) 0
  )"

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
    consumed_time = 0,
    cur_time = 0,
    cur_sc = idle_sc_ptr,
    reprogram_timer = False,
    scheduler_action = resume_cur_thread,
    domain_list = [(0,15)],
    domain_index = 0,
    cur_domain = 0,
    domain_time = 15,
    ready_queues = const (const []),
    release_queue = [],
    machine_state = init_machine_state,
    interrupt_irq_node = \<lambda>irq. init_irq_node_ptr + (ucast irq << cte_level_bits),
    interrupt_states = \<lambda>_. Structures_A.IRQInactive,
    arch_state = init_arch_state,
    exst = ext_init
  \<rparr>"

end

end
