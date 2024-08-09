(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterrupt_H
imports
  RetypeDecls_H
  CNode_H
  InterruptDecls_H
  ArchInterruptDecls_H
  ArchHypervisor_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Object/Interrupt/ARM.lhs Arch= CONTEXT ARM_H bodies_only ArchInv=

end
end
