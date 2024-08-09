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

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures/RISCV64.hs

#INCLUDE_HASKELL SEL4/API/Invocation/RISCV64.hs CONTEXT RISCV64_H decls_only NOT Invocation IRQControlInvocation

#INCLUDE_HASKELL SEL4/API/Invocation/RISCV64.hs CONTEXT RISCV64_H decls_only ONLY Invocation IRQControlInvocation

#INCLUDE_HASKELL SEL4/Object/ObjectType/RISCV64.hs CONTEXT RISCV64_H Arch.Types=ArchTypes_H ArchInv= decls_only

end (*context RISCV64*)

(* Defined differently and/or delayed on different architectures *)
consts canonicalAddressAssert :: "machine_word => bool"

end
