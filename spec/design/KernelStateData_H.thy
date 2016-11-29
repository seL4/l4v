(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file KernelStateData_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
	Kernel state and kernel monads, imports everything that SEL4.Model needs.
*)

chapter "Kernel State and Monads"

theory KernelStateData_H
imports
  PSpaceStruct_H
  Structures_H
  "../machine/$L4V_ARCH/MachineOps"
  "./$L4V_ARCH/ArchStateData_H"
begin

context begin interpretation Arch .

requalify_types
  vmpage_size

end

requalify_types (in Arch)
  kernel_state

subsection "The Kernel State"

type_synonym ready_queue = "machine_word list"
translations
(type) "machine_word list" <= (type) "ready_queue"

text {* We pull a fast one on haskell here ... although Haskell expects
a KernelMonad which is a StateT monad in KernelData that wraps a MachineMonad,
we push the extra MachineMonad data into the KernelState. Fortunately the
update and accessor functions all still work. *}

record kernel_state =
  ksPSpace             :: pspace
  gsUserPages          :: "machine_word \<Rightarrow> vmpage_size option"
  gsCNodes             :: "machine_word \<Rightarrow> nat option"
  gsUntypedZeroRanges  :: "(machine_word \<times> machine_word) set"
  gsMaxObjectSize      :: nat
  ksDomScheduleIdx     :: nat
  ksDomSchedule        :: "(domain \<times> machine_word) list"
  ksCurDomain          :: domain
  ksDomainTime         :: machine_word
  ksReadyQueues        :: "domain \<times> priority \<Rightarrow> ready_queue"
  ksReadyQueuesL1Bitmap :: "domain \<Rightarrow> machine_word"
  ksReadyQueuesL2Bitmap :: "domain \<times> nat \<Rightarrow> machine_word"
  ksCurThread          :: machine_word
  ksIdleThread         :: machine_word
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

definition
getCurThread :: "(machine_word) kernel"
where
"getCurThread \<equiv> gets ksCurThread"

definition
setCurThread :: "machine_word \<Rightarrow> unit kernel"
where
"setCurThread tptr\<equiv> modify (\<lambda> ks. ks \<lparr> ksCurThread := tptr \<rparr>)"

definition
getIdleThread :: "(machine_word) kernel"
where
"getIdleThread \<equiv> gets ksIdleThread"

definition
setIdleThread :: "machine_word \<Rightarrow> unit kernel"
where
"setIdleThread tptr\<equiv> modify (\<lambda> ks. ks \<lparr> ksIdleThread := tptr \<rparr>)"

definition
getQueue :: "domain \<Rightarrow> priority \<Rightarrow> ready_queue kernel"
where
"getQueue qdom prio\<equiv> gets (\<lambda> ks. ksReadyQueues ks (qdom, prio))"

definition
setQueue :: "domain \<Rightarrow> priority \<Rightarrow> ready_queue \<Rightarrow> unit kernel"
where
"setQueue qdom prio q\<equiv> modify (\<lambda> ks. ks \<lparr> ksReadyQueues := (ksReadyQueues ks) aLU [((qdom, prio),q)] \<rparr>)"

definition
getSchedulerAction :: "scheduler_action kernel"
where
"getSchedulerAction \<equiv> gets ksSchedulerAction"

definition
setSchedulerAction :: "scheduler_action \<Rightarrow> unit kernel"
where
"setSchedulerAction a\<equiv> modify (\<lambda> ks. ks \<lparr> ksSchedulerAction := a \<rparr>)"

definition
getInterruptState :: "interrupt_state kernel"
where
"getInterruptState \<equiv> gets ksInterruptState"

definition
setInterruptState :: "interrupt_state \<Rightarrow> unit kernel"
where
"setInterruptState a\<equiv> modify (\<lambda> ks. ks \<lparr> ksInterruptState := a \<rparr>)"

definition
getWorkUnits :: "machine_word kernel"
where
"getWorkUnits \<equiv> gets ksWorkUnitsCompleted"

definition
setWorkUnits :: "machine_word \<Rightarrow> unit kernel"
where
"setWorkUnits a\<equiv> modify (\<lambda> ks. ks \<lparr> ksWorkUnitsCompleted := a \<rparr>)"

definition
modifyWorkUnits :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> unit kernel"
where
"modifyWorkUnits f\<equiv> modify (\<lambda> ks. ks \<lparr> ksWorkUnitsCompleted :=
                                        f (ksWorkUnitsCompleted ks) \<rparr>)"

definition
curDomain :: "domain kernel"
where
"curDomain \<equiv> gets ksCurDomain"

definition
nextDomain :: "unit kernel"
where
"nextDomain\<equiv> modify (\<lambda> ks.
  let ksDomScheduleIdx' = (ksDomScheduleIdx ks + 1) mod length (ksDomSchedule ks) in
  let next = ksDomSchedule ks ! ksDomScheduleIdx'
  in ks \<lparr> ksWorkUnitsCompleted := 0,
          ksDomScheduleIdx := ksDomScheduleIdx',
          ksCurDomain := dschDomain next,
          ksDomainTime := dschLength next \<rparr>)"

definition
getDomainTime :: "machine_word kernel"
where
"getDomainTime \<equiv> gets ksDomainTime"

definition
decDomainTime :: "unit kernel"
where
"decDomainTime\<equiv> modify (\<lambda> ks. ks \<lparr> ksDomainTime := ksDomainTime ks - 1 \<rparr>)"

consts'
capHasProperty :: "machine_word \<Rightarrow> (capability \<Rightarrow> bool) \<Rightarrow> kernel_state \<Rightarrow> bool"


end
