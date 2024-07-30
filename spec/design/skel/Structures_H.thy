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

#INCLUDE_HASKELL SEL4/Object/Structures.lhs decls_only NOT isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isNotificationCap
#INCLUDE_HASKELL SEL4/Object/Structures.lhs bodies_only NOT kernelObjectTypeName isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isNotificationCap


end
