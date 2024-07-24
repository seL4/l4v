(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Init_R
imports
  KHeap_R

begin

context begin interpretation Arch . (*FIXME: arch-split*)

(*
  This provides a very simple witness that the state relation used in the first refinement proof is
  non-trivial, by exhibiting a pair of related states. This helps guard against silly mistakes in
  the state relation, since we currently assume that the system starts in a state satisfying
  invariants and state relations.

  Note that the states we exhibit are not intended to be useful states. They are just the simplest
  possible states that prove non-triviality of the state relation. In particular, these states do
  not satisfy the respective invariant conditions. In future, this could be improved by exhibiting
  a tuple of more realistic states that are related across all levels of the refinement, and that
  also satisfy respective invariant. Ultimately, we would like to prove functional correctness of
  kernel initialisation. That would allow us to start from a minimal but real configuration that
  would allow us to make a much smaller set of assumptions about the initial configuration of the
  system.
*)

definition zeroed_arch_abstract_state ::
  arch_state
  where
  "zeroed_arch_abstract_state \<equiv> \<lparr>
    arm_asid_table    = Map.empty,
    arm_kernel_vspace = K ArmVSpaceUserRegion,
    arm_vmid_table = Map.empty,
    arm_next_vmid = 0,
    arm_us_global_vspace = 0,
    arm_current_vcpu = None,
    arm_gicvcpu_numlistregs = 0
  \<rparr>"

definition zeroed_main_abstract_state ::
  abstract_state
  where
  "zeroed_main_abstract_state \<equiv> \<lparr>
    kheap = Map.empty,
    cdt = Map.empty,
    is_original_cap = \<top>,
    cur_thread = 0,
    idle_thread = 0,
    machine_state = init_machine_state,
    interrupt_irq_node = (\<lambda>irq. ucast irq << cte_level_bits),
    interrupt_states = (K irq_state.IRQInactive),
    arch_state = zeroed_arch_abstract_state
  \<rparr>"

definition zeroed_extended_state ::
  det_ext
  where
  "zeroed_extended_state \<equiv> \<lparr>
    work_units_completed_internal = 0,
    scheduler_action_internal = resume_cur_thread,
    ekheap_internal = Map.empty,
    domain_list_internal = [],
    domain_index_internal = 0,
    cur_domain_internal = 0,
    domain_time_internal = 0,
    ready_queues_internal = (\<lambda>_ _. []),
    cdt_list_internal = K []
  \<rparr>"

definition zeroed_abstract_state ::
  det_state
  where
  "zeroed_abstract_state \<equiv> abstract_state.extend zeroed_main_abstract_state
                           (state.fields zeroed_extended_state)"

definition zeroed_arch_intermediate_state ::
  Arch.kernel_state
  where
  "zeroed_arch_intermediate_state \<equiv>
    ARMKernelState Map.empty (K ArmVSpaceUserRegion)
                   Map.empty 0 0 None 0 Map.empty"

definition zeroed_intermediate_state ::
  global.kernel_state
  where
  "zeroed_intermediate_state \<equiv> \<lparr>
    ksPSpace = Map.empty,
    gsUserPages = Map.empty,
    gsCNodes = Map.empty,
    gsUntypedZeroRanges = {},
    gsMaxObjectSize = 0,
    ksDomScheduleIdx = 0,
    ksDomSchedule = [],
    ksCurDomain = 0,
    ksDomainTime = 0,
    ksReadyQueues = K (TcbQueue None None),
    ksReadyQueuesL1Bitmap = K 0,
    ksReadyQueuesL2Bitmap = K 0,
    ksCurThread = 0,
    ksIdleThread = 0,
    ksSchedulerAction = ResumeCurrentThread,
    ksInterruptState = (InterruptState 0 (K IRQInactive)),
    ksWorkUnitsCompleted = 0,
    ksArchState = zeroed_arch_intermediate_state,
    ksMachineState = init_machine_state
  \<rparr>"

lemmas zeroed_state_defs = zeroed_main_abstract_state_def zeroed_abstract_state_def
                           zeroed_arch_abstract_state_def zeroed_extended_state_def
                           zeroed_intermediate_state_def abstract_state.defs
                           zeroed_arch_intermediate_state_def

lemma non_empty_refine_state_relation:
  "(zeroed_abstract_state, zeroed_intermediate_state) \<in> state_relation"
  apply (clarsimp simp: state_relation_def zeroed_state_defs state.defs)
  apply (intro conjI)
          apply (clarsimp simp: pspace_relation_def pspace_dom_def)
         apply (clarsimp simp: ekheap_relation_def)
        apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def queue_end_valid_def
                              opt_pred_def list_queue_relation_def tcbQueueEmpty_def
                              prev_queue_head_def)
       apply (clarsimp simp: ghost_relation_def)
      apply (fastforce simp: cdt_relation_def swp_def dest: cte_wp_at_domI)
     apply (clarsimp simp: cdt_list_relation_def map_to_ctes_def)
    apply (clarsimp simp: revokable_relation_def map_to_ctes_def)
   apply (clarsimp simp: zeroed_state_defs arch_state_relation_def)
  apply (clarsimp simp: interrupt_state_relation_def irq_state_relation_def cte_level_bits_def)
  done

end
end
