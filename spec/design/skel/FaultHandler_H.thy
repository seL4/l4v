(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Fault Handlers"

theory FaultHandler_H
imports
  FaultHandlerDecls_H
  TCB_H
  ArchFaultHandler_H
begin

arch_requalify_consts (H)
  makeArchFaultMessage
  handleArchFaultReply

(* clobbers previously requalified abstract spec constants with design spec versions *)
arch_requalify_consts (aliasing, H)
  syscallMessage
  exceptionMessage

#INCLUDE_HASKELL_PREPARSE SEL4/API/Failures.lhs

#INCLUDE_HASKELL SEL4/Kernel/FaultHandler.lhs bodies_only
#INCLUDE_HASKELL SEL4/API/Faults.lhs decls_only
#INCLUDE_HASKELL SEL4/API/Faults.lhs bodies_only

end
