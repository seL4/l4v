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
   datatypes/records for the various kernel data structures.
*)

chapter "Kernel Data Structures"

theory Structures_H
imports
  Config_H
  "./$L4V_ARCH/State_H"
  Fault_H
  Types_H
  "./$L4V_ARCH/ArchStructures_H"
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

#INCLUDE_HASKELL SEL4/Object/Structures.lhs decls_only NOT isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isNotificationCap
#INCLUDE_HASKELL SEL4/Object/Structures.lhs bodies_only NOT kernelObjectTypeName isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isNotificationCap


end
