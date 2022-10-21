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

context begin interpretation Arch .

requalify_types
  irq
  arch_capability
  user_context
  arch_kernel_object
  asid
  arch_tcb

requalify_consts
  archObjSize
  pageBits
  nullPointer
  newArchTCB
  fromPPtr
  PPtr
  atcbContextGet
  atcbContextSet

end

#INCLUDE_HASKELL SEL4/Object/Structures.lhs decls_only NOT isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isNotificationCap isThreadCap isSchedContextCap objBitsKO
#INCLUDE_HASKELL SEL4/Object/Structures.lhs bodies_only NOT kernelObjectTypeName isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isNotificationCap isThreadCap isSchedContextCap objBitsKO

#INCLUDE_HASKELL SEL4/Object/Structures.lhs decls_only ONLY objBitsKO
#INCLUDE_HASKELL SEL4/Object/Structures.lhs bodies_only ONLY objBitsKO


end
