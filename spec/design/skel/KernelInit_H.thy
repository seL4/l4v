(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Initialisation"

theory KernelInit_H
imports
  KI_Decls_H
  ArchRetype_H
  Retype_H
  Config_H
  Thread_H
begin

arch_requalify_consts
  getMemoryRegions
  addrFromPPtr
  init_machine_state

requalify_consts (in Arch)
  newKernelState

fun coverOf :: "region list => region"
where "coverOf x0 = (case x0 of
    [] =>    Region (0,0)
  | [x] =>    x
  | (x#xs) =>
    let
        (l,h) = fromRegion x;
        (ll,hh) = fromRegion $ coverOf xs;
        ln = if l \<le> ll then l else ll;
        hn = if h \<le> hh then hh else h
    in
    Region (ln, hn)
  )"

definition syncBIFrame :: "unit kernel_init"
where "syncBIFrame \<equiv> returnOk ()"

#INCLUDE_HASKELL SEL4/Kernel/Init.lhs bodies_only NOT isAligned funArray newKernelState distinct rangesBy InitData doKernelOp runInit noInitFailure coverOf foldME

consts
  newKSDomSchedule :: "(domain \<times> machine_word) list"
  newKSDomScheduleIdx :: nat
  newKSCurDomain :: domain
  newKSDomainTime :: machine_word
  newKernelState :: "machine_word \<Rightarrow> kernel_state"

defs
newKernelState_def:
"newKernelState data_start \<equiv> \<lparr>
        ksPSpace = newPSpace,
        gsUserPages = (\<lambda>x. None),
        gsCNodes = (\<lambda>x. None),
        gsUntypedZeroRanges = {},
        gsMaxObjectSize = card (UNIV :: machine_word set),
        ksDomScheduleIdx = newKSDomScheduleIdx,
        ksDomSchedule = newKSDomSchedule,
        ksCurDomain = newKSCurDomain,
        ksDomainTime = newKSDomainTime,
        ksReadyQueues = const (TcbQueue None None),
        ksReadyQueuesL1Bitmap = const 0,
        ksReadyQueuesL2Bitmap = const 0,
        ksCurThread = error [],
        ksIdleThread = error [],
        ksSchedulerAction = ResumeCurrentThread,
        ksInterruptState = error [],
        ksWorkUnitsCompleted = 0,
        ksArchState = fst (Arch.newKernelState data_start),
        ksMachineState = init_machine_state
\<rparr>"

(* disambiguate name clash between Arch and non-arch consts with same names *)
context Arch begin
requalify_facts (aliasing)
   newKernelState_def
requalify_consts (aliasing)
   newKernelState

context begin global_naming global
requalify_facts (aliasing)
   KernelInit_H.newKernelState_def
requalify_consts (aliasing)
   KernelInit_H.newKernelState
end
end

end
