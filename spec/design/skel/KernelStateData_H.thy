(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Kernel state and kernel monads, imports everything that SEL4.Model needs.
*)

chapter "Kernel State and Monads"

theory KernelStateData_H
imports
  PSpaceStruct_H
  Structures_H
  MachineOps
  ArchStateData_H
begin

arch_requalify_consts (H)
  usToTicks

requalify_types (in Arch)
  kernel_state

subsection "The Kernel State"

type_synonym ready_queue = tcb_queue

type_synonym release_queue = tcb_queue

text \<open>We pull a fast one on haskell here ... although Haskell expects
a KernelMonad which is a StateT monad in KernelData that wraps a MachineMonad,
we push the extra MachineMonad data into the KernelState. Fortunately the
update and accessor functions all still work.\<close>

record kernel_state =
  ksPSpace             :: pspace
  gsUserPages          :: "machine_word \<Rightarrow> vmpage_size option"
  gsCNodes             :: "machine_word \<Rightarrow> nat option"
  gsUntypedZeroRanges  :: "(machine_word \<times> machine_word) set"
  gsMaxObjectSize      :: nat
  ksDomScheduleIdx     :: nat
  ksDomSchedule        :: "(domain \<times> time) list"
  ksCurDomain          :: domain
  ksDomainTime         :: time
  ksReadyQueues        :: "domain \<times> priority \<Rightarrow> ready_queue"
  ksReleaseQueue       :: release_queue
  ksReadyQueuesL1Bitmap :: "domain \<Rightarrow> machine_word"
  ksReadyQueuesL2Bitmap :: "domain \<times> nat \<Rightarrow> machine_word"
  ksCurThread          :: machine_word
  ksIdleThread         :: machine_word
  ksIdleSC             :: machine_word
  ksConsumedTime       :: time
  ksCurTime            :: time
  ksCurSc              :: machine_word
  ksReprogramTimer     :: bool
  ksSchedulerAction    :: scheduler_action
  ksInterruptState     :: interrupt_state
  ksWorkUnitsCompleted :: machine_word
  ksArchState          :: Arch.kernel_state
  ksMachineState       :: machine_state

context Arch begin
context begin global_naming global
requalify_types KernelStateData_H.kernel_state
end
end

type_synonym 'a kernel = "(kernel_state, 'a) nondet_monad"

translations
  (type) "'c kernel" <= (type) "(kernel_state, 'c) nondet_monad"

type_synonym 'a kernel_r = "(kernel_state, 'a) lookup"

translations
  (type) "'c kernel_r" <= (type) "(kernel_state, 'c) lookup"

subsection "Kernel Functions"

subsubsection "Initial Kernel State"

definition
  doMachineOp :: "(machine_state, 'a) nondet_monad  \<Rightarrow> 'a kernel"
where
 "doMachineOp mop \<equiv> do
    ms \<leftarrow> gets ksMachineState;
    (r, ms') \<leftarrow> select_f (mop ms);
    modify (\<lambda>ks. ks \<lparr> ksMachineState := ms' \<rparr>);
    return r
  od"

#INCLUDE_HASKELL SEL4/Model/StateData.lhs decls_only ONLY capHasProperty sym_refs_asrt valid_replies'_sc_asrt ready_qs_runnable tcs_cross_asrt1 tcs_cross_asrt2 ct_not_inQ_asrt sch_act_wf_asrt valid_idle'_asrt cur_tcb'_asrt sch_act_sane_asrt ct_not_ksQ_asrt ct_active'_asrt rct_imp_activatable'_asrt ct_activatable'_asrt ready_or_release'_asrt findTimeAfter_asrt not_tcbInReleaseQueue_asrt tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt tcbQueueHead_ksReleaseQueue_active_sc_tcb_at'_asrt not_tcbQueued_asrt ksReadyQueues_asrt ksReleaseQueue_asrt idleThreadNotQueued sc_at'_asrt valid_tcbs'_asrt
#INCLUDE_HASKELL SEL4/Model/StateData.lhs NOT doMachineOp KernelState ReadyQueue ReleaseQueue ReaderM Kernel KernelR getsJust assert stateAssert funOfM condition whileLoop findM funArray newKernelState capHasProperty ifM whenM whileM andM orM sym_refs_asrt valid_replies'_sc_asrt ready_qs_runnable tcs_cross_asrt1 tcs_cross_asrt2 ct_not_inQ_asrt sch_act_wf_asrt valid_idle'_asrt cur_tcb'_asrt sch_act_sane_asrt ct_not_ksQ_asrt ct_active'_asrt rct_imp_activatable'_asrt ct_activatable'_asrt ready_or_release'_asrt findTimeAfter_asrt not_tcbInReleaseQueue_asrt tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt tcbQueueHead_ksReleaseQueue_active_sc_tcb_at'_asrt not_tcbQueued_asrt ksReadyQueues_asrt ksReleaseQueue_asrt idleThreadNotQueued sc_at'_asrt valid_tcbs'_asrt

end
