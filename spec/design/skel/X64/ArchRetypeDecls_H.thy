(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

theory ArchRetypeDecls_H
imports
  FaultMonad_H
  EndpointDecls_H
  KernelInitMonad_H
  PSpaceFuns_H
  ArchObjInsts_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/API/Invocation/X64.lhs CONTEXT X64_H decls_only NOT Invocation IRQControlInvocation

#INCLUDE_HASKELL SEL4/API/Invocation/X64.lhs CONTEXT X64_H decls_only ONLY Invocation IRQControlInvocation

#INCLUDE_HASKELL SEL4/Object/ObjectType/X64.lhs CONTEXT X64_H Arch.Types=ArchTypes_H ArchInv= decls_only

end (*context X64*)

(* Defined differently and/or delayed on different architectures *)
definition
  canonicalAddressAssert :: "machine_word => bool" where
  canonicalAddressAssert_def[simp]:
  "canonicalAddressAssert p = True"

end
