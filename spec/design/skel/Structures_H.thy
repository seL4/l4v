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
  State_H
  Fault_H
  Types_H
  ARMStructures_H
begin

#INCLUDE_HASKELL SEL4/Object/Structures.lhs decls_only NOT isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isAsyncEndpointCap
#INCLUDE_HASKELL SEL4/Object/Structures.lhs bodies_only NOT kernelObjectTypeName isNullCap isUntypedCap isIRQControlCap isReplyCap isDomainCap isAsyncEndpointCap


end
