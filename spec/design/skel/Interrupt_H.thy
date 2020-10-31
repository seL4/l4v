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

requalify_consts
  checkIRQ
  decodeIRQControlInvocation
  performIRQControl
  invokeIRQHandler
  initInterruptController
  handleReservedIRQ
  maskIrqSignal

context begin global_naming global
requalify_consts
  InterruptDecls_H.decodeIRQControlInvocation
  InterruptDecls_H.performIRQControl
end

end

context begin interpretation Arch .

requalify_consts
  maxIRQ
  minIRQ
  maskInterrupt
  ackInterrupt
  resetTimer
  debugPrint

end

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs
#INCLUDE_HASKELL SEL4/Object/Interrupt.lhs bodies_only

end
