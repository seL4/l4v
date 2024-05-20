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

context Arch begin global_naming ARM_HYP_H

(* Kernel_Config provides a generic numeral, Haskell expects type irq *)
abbreviation (input) maxIRQ :: irq where
  "maxIRQ == Kernel_Config.maxIRQ"

#INCLUDE_HASKELL SEL4/Object/Interrupt/ARM.lhs Arch= CONTEXT ARM_HYP_H bodies_only ArchInv= NOT initInterruptController

definition initInterruptController :: "unit kernel"
  where "initInterruptController \<equiv> (do
    setIRQState IRQReserved $ irqVGICMaintenance;
    return ()
od)"

end
end
