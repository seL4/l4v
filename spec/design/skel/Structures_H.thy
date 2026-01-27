(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   datatypes/records for the various kernel data structures.
*)

chapter "Kernel Data Structures"

theory Structures_H
imports
  Structs_B
  Config_H
  State_H
  Fault_H
  Types_H
  ArchStructures_H
begin

arch_requalify_types (H)
  arch_capability
  arch_kernel_object
  asid
  arch_tcb

arch_requalify_consts (H)
  archObjSize
  nullPointer
  newArchTCB
  fromPPtr
  PPtr
  atcbContextGet
  atcbContextSet

type_synonym tcb_queue = "machine_word head_end_ptrs"

abbreviation (input) tcbQueueHead :: "tcb_queue \<Rightarrow> machine_word option" where
  "tcbQueueHead \<equiv> he_ptrs_head"

abbreviation (input) tcbQueueHead_update ::
  "(machine_word option \<Rightarrow> machine_word option) \<Rightarrow> tcb_queue \<Rightarrow> tcb_queue" where
  "tcbQueueHead_update \<equiv> he_ptrs_head_update"

abbreviation (input) tcbQueueEnd :: "tcb_queue \<Rightarrow> machine_word option" where
  "tcbQueueEnd \<equiv> he_ptrs_end"

abbreviation (input) tcbQueueEnd_update ::
  "(machine_word option \<Rightarrow> machine_word option) \<Rightarrow> tcb_queue \<Rightarrow> tcb_queue" where
  "tcbQueueEnd_update \<equiv> he_ptrs_end_update"

abbreviation (input) emptyQueue :: tcb_queue where
  "emptyQueue \<equiv> emptyHeadEndPtrs"

abbreviation (input) tcbQueueEmpty :: "tcb_queue \<Rightarrow> bool" where
  "tcbQueueEmpty \<equiv> headEndPtrsEmpty"

#INCLUDE_HASKELL SEL4/Object/Structures.lhs decls_only NOT isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isNotificationCap TcbFlag tcbFlagToWord tcbFlagMask TcbQueue emptyQueue
#INCLUDE_HASKELL SEL4/Object/Structures.lhs bodies_only NOT kernelObjectTypeName isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isNotificationCap tcbFlagToWord tcbFlagMask TcbQueue emptyQueue


end
