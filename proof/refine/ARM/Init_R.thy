

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

end
end
