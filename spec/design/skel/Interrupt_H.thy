(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Interrupt_H
imports
  RetypeDecls_H
  ArchInterrupt_H
  Notification_H
  CNode_H
  KI_Decls_H
  InterruptDecls_H
begin

context Arch begin

(* match Haskell, expects these under Arch. *)
requalify_consts
  checkIRQ
  handleReservedIRQ
  maskIrqSignal

(* disambiguate name clash between Arch and non-arch consts with same names *)
requalify_consts (aliasing)
  decodeIRQControlInvocation
  invokeIRQHandler
  performIRQControl
  initInterruptController

context begin global_naming global
requalify_consts (aliasing)
  InterruptDecls_H.decodeIRQControlInvocation
  InterruptDecls_H.invokeIRQHandler
  InterruptDecls_H.performIRQControl
  InterruptDecls_H.initInterruptController

end
end

arch_requalify_consts
  deadlineIRQ

(* override Kernel_Config const with constrained abbreviation from Hardware_H *)
arch_requalify_consts (aliasing, H)
  maxIRQ

arch_requalify_consts (H)
  handleSpuriousIRQ

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs
#INCLUDE_HASKELL SEL4/Object/Interrupt.lhs bodies_only

end
