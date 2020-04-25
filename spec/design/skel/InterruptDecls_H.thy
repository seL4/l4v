(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory InterruptDecls_H
imports
  RetypeDecls_H
  KI_Decls_H
begin

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs
#INCLUDE_HASKELL SEL4/Object/Interrupt.lhs Arch=ArchInterrupt_H decls_only NOT deletedIRQHandler

end
