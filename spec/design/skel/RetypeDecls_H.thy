(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Function Declarations for Retyping Objects"

theory RetypeDecls_H
imports
  ArchRetypeDecls_H
  Structures_H
  FaultMonad_H
  Invocations_H
begin

#INCLUDE_HASKELL SEL4/Object/ObjectType.lhs decls_only

#INCLUDE_HASKELL SEL4/Object/Interrupt.lhs decls_only ONLY deletedIRQHandler

end
