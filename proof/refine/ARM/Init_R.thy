

chapter \<open>Abstract datatype for the executable specification\<close>

theory Init_R
imports
  KHeap_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

definition
  "zeroed_arch_abstract_state \<equiv> \<lparr>
    arm_asid_table = Map.empty,
    arm_hwasid_table = Map.empty,
    arm_next_asid = 0,
    arm_asid_map = Map.empty,
    arm_global_pd = 0,
    arm_global_pts = [],
    arm_kernel_vspace = K ArmVSpaceUserRegion
  \<rparr>"

definition
  "zeroed_abstract_state \<equiv>
  \<lparr>kheap = Map.empty,
  cdt = Map.empty,
  is_original_cap = (K True),
  cur_thread = 0,
  idle_thread = 0,
  consumed_time = 0,
  cur_time = 0,
  cur_sc = 0,
  reprogram_timer = True,
  scheduler_action = resume_cur_thread,
  domain_list = [],
  domain_index = 0,
  cur_domain = 0,
  domain_time = 0,
  ready_queues = (\<lambda>_ _. []),
  release_queue = [],
  machine_state = init_machine_state,
  interrupt_irq_node = (\<lambda>irq. ucast irq << cte_level_bits),
  interrupt_states = (K irq_state.IRQInactive),
  arch_state = zeroed_arch_abstract_state\<rparr> :: abstract_state"

definition zeroed_extended_state :: det_ext where
  "zeroed_extended_state \<equiv>
   \<lparr>work_units_completed_internal = 0,
    cdt_list_internal = K []\<rparr>"

definition zeroed_det_state :: det_state where
  "zeroed_det_state \<equiv> abstract_state.extend zeroed_abstract_state (state.fields zeroed_extended_state)"

definition
 "zeroed_arch_kernel_state \<equiv> ARMKernelState Map.empty Map.empty 0 Map.empty 0 [] (K ArmVSpaceUserRegion)"

definition
 "zeroed_kernel_state \<equiv>
 \<lparr>ksPSpace = Map.empty,
  gsUserPages = Map.empty,
  gsCNodes = Map.empty,
  gsUntypedZeroRanges = {},
  gsMaxObjectSize = 0,
  ksDomScheduleIdx = 0,
  ksDomSchedule = [],
  ksCurDomain = 0,
  ksDomainTime = 0,
  ksReadyQueues = K [],
  ksReleaseQueue = [],
  ksReadyQueuesL1Bitmap = K 0,
  ksReadyQueuesL2Bitmap = K 0,
  ksCurThread = 0,
  ksIdleThread = 0,
  ksConsumedTime = 0,
  ksCurTime = 0,
  ksCurSc = 0,
  ksReprogramTimer = True,
  ksSchedulerAction = ResumeCurrentThread,
  ksInterruptState = (InterruptState 0 (K IRQInactive)),
  ksWorkUnitsCompleted = 0,
  ksArchState = zeroed_arch_kernel_state,
  ksMachineState = init_machine_state\<rparr>"

lemmas zeroed_state_defs = zeroed_det_state_def zeroed_abstract_state_def
                           zeroed_arch_abstract_state_def zeroed_extended_state_def
                           zeroed_kernel_state_def abstract_state.defs zeroed_arch_kernel_state_def

lemma non_empty_refine_state_relation:
  "(zeroed_det_state, zeroed_kernel_state) \<in> state_relation"
  apply (clarsimp simp: state_relation_def zeroed_state_defs
                        state.defs)
  apply (intro conjI)
           apply (clarsimp simp: pspace_relation_def pspace_dom_def)
          apply (clarsimp simp: sc_replies_relation_def vs_all_heap_simps)
         apply (clarsimp simp: ready_queues_relation_def)
        apply (clarsimp simp: release_queue_relation_def)
       apply (clarsimp simp: ghost_relation_def)
      apply (fastforce simp: cdt_relation_def swp_def dest: cte_wp_at_domI)
     apply (clarsimp simp: cdt_list_relation_def map_to_ctes_def)
    apply (clarsimp simp: revokable_relation_def map_to_ctes_def)
   apply (clarsimp simp: zeroed_state_defs arch_state_relation_def)
  apply (clarsimp simp: interrupt_state_relation_def irq_state_relation_def cte_level_bits_def)
  done



(* definition
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
    tcb_domain = 0,
    tcb_arch = init_arch_tcb
  \<rparr>,
  init_globals_frame \<mapsto> ArchObj (DataPage False ARMSmallPage), \<comment> \<open>FIXME: same reason as why we kept the definition of @{text init_globals_frame}\<close>
  init_global_pd \<mapsto> ArchObj (PageDirectory global_pd),
  idle_sc_ptr \<mapsto> SchedContext (default_sched_context
                                 \<lparr>sc_tcb := Some idle_thread_ptr,
                                  sc_refills := [\<lparr>r_time = 0, r_amount = 0\<rparr>],
                                  sc_refill_max := MIN_REFILLS\<rparr>) 0
  )" *)

definition
  "init_ksPSpace \<equiv> (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
       then Some (CNode 0 (empty_cnode 0)) else None) "

term init_arch_state
definition
 "init_ksArchState \<equiv> ARMKernelState Map.empty Map.empty 0 Map.empty init_global_pd [] (\<lambda>ref.
      if ref \<in> {kernel_base .. kernel_base + mask 20}
      then ArmVSpaceKernelWindow
      else ArmVSpaceInvalidRegion)"

definition
 "init_H_st \<equiv>
 \<lparr>ksPSpace = Map.empty,
  gsUserPages = Map.empty,
  gsCNodes = Map.empty,
  gsUntypedZeroRanges = {},
  gsMaxObjectSize = 0,
  ksDomScheduleIdx = 0,
  ksDomSchedule = [(0,15)],
  ksCurDomain = 0,
  ksDomainTime = 15,
  ksReadyQueues = K [],
  ksReleaseQueue = [],
  ksReadyQueuesL1Bitmap = K 0,
  ksReadyQueuesL2Bitmap = K 0,
  ksCurThread = idle_thread_ptr,
  ksIdleThread = idle_thread_ptr,
  ksConsumedTime = 0,
  ksCurTime = 0,
  ksCurSc = idle_sc_ptr,
  ksReprogramTimer = False,
  ksSchedulerAction = ResumeCurrentThread,
  ksInterruptState = (InterruptState init_irq_node_ptr (K IRQInactive)),
  ksWorkUnitsCompleted = 0,
  ksArchState = init_ksArchState,
  ksMachineState = init_machine_state\<rparr>"

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
    tcb_domain = 0,
    tcb_arch = init_arch_tcb

    Thread (tcbCTable : cte) (tcbVTable : cte) (tcbIPCBufferFrame : cte)
(tcbFaultHandler : cte) (tcbTimeoutHandler : cte) (tcbDomain : domain)
(tcbState : thread_state) (tcbMCP : priority) (tcbPriority : priority)
(tcbQueued : bool) (tcbInReleaseQueue : bool) (tcbFault : "fault option")
 (tcbIPCBuffer : vptr) (tcbBoundNotification : "(machine_word) option")
(tcbSchedContext : "(machine_word) option") (tcbYieldTo : "(machine_word) option") (tcbArch : arch_tcb)

typ cte

term NullCap
term state_relation
definition
  "init_iisdfkheapf \<equiv> Thread a b c d e 0 g h 0 False False None 0 None (Some idle_sc_ptr) None q"


definition
  "init_kheapf \<equiv>
  (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
       then Some (KOCTE tcb) else None)
  (idle_thread_ptr \<mapsto> (KOTCB (Thread a b c d e 0 g h 0 False False None 0 None (Some idle_sc_ptr) None q)))"

term init_kheap
definition
  "init_H_st \<equiv> \<lparr>
    kheap = init_kheap,
    cdt = init_cdt,
    is_original_cap = init_ioc,
    exst = ext_init
  \<rparr>"

lemmas init_state_defs = init_H_st_def init_A_st_def ext_init_def

lemma empty_opt_map_left:
  "Map.empty |> g = Map.empty"
  by (clarsimp simp: opt_map_def)


find_theorems Map.empty opt_map -valid
term ksPSpace
find_theorems Structures_H.kernel_object
term ksPSpace

lemma init_refine_state_relation:
  "(init_A_st, init_H_st) \<in> state_relation"
  apply (clarsimp simp: state_relation_def init_state_defs
                        state.defs)
  apply (intro conjI)
          apply (clarsimp simp: pspace_relation_def)



  subgoal sorry
          apply (clarsimp simp: sc_replies_relation_def vs_all_heap_simps init_kheap_def default_sched_context_def
                    empty_opt_map_left)
         apply (clarsimp simp: ready_queues_relation_def const_def)
        apply (clarsimp simp: release_queue_relation_def)
  subgoal sorry
      apply (clarsimp simp: cdt_relation_def swp_def init_cdt_def map_to_ctes_def
      descendants_of_def descendants_of'_def)
  subgoal sorry (* ouch *)
     apply (clarsimp simp: cdt_list_relation_def map_to_ctes_def)
    apply (clarsimp simp: revokable_relation_def map_to_ctes_def)
   apply (clarsimp simp: init_ksArchState_def init_arch_state_def arch_state_relation_def)
  apply (clarsimp simp: interrupt_state_relation_def irq_state_relation_def cte_level_bits_def)
  done

end
end
