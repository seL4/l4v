(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

theory ArchRetypeDecls_H
imports
  ArchLabelFuns_H
  FaultMonad_H
  EndpointDecls_H
  KernelInitMonad_H
  PSpaceFuns_H
  ArchObjInsts_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/API/Invocation/ARM.lhs CONTEXT ARM_H decls_only NOT isPageFlushLabel isPDFlushLabel Invocation IRQControlInvocation CopyRegisterSets

#INCLUDE_HASKELL SEL4/API/Invocation/ARM.lhs CONTEXT ARM_H decls_only ONLY Invocation IRQControlInvocation CopyRegisterSets

#INCLUDE_HASKELL SEL4/Object/ObjectType/ARM.lhs CONTEXT ARM_H Arch.Types=ArchTypes_H ArchInv= decls_only

end

(* Defined differently and/or delayed on different architectures *)
definition
  canonicalAddressAssert :: "machine_word => bool" where
  canonicalAddressAssert_def[simp]:
  "canonicalAddressAssert p = True"

end
