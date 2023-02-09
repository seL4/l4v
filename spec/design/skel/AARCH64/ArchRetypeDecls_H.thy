(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2022, Proofcraft Pty Ltd
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

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures/AARCH64.hs

#INCLUDE_HASKELL SEL4/API/Invocation/AARCH64.hs CONTEXT AARCH64_H decls_only \
  NOT Invocation IRQControlInvocation isVSpaceFlushLabel isPageFlushLabel FlushType

#INCLUDE_HASKELL SEL4/API/Invocation/AARCH64.hs CONTEXT AARCH64_H decls_only ONLY Invocation IRQControlInvocation

#INCLUDE_HASKELL SEL4/Object/ObjectType/AARCH64.hs CONTEXT AARCH64_H Arch.Types=ArchTypes_H ArchInv= decls_only

end (*context AARCH64*)

(* Defined differently and/or delayed on different architectures *)
consts canonicalAddressAssert :: "machine_word => bool"

end
