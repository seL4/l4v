(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Threads"

theory Thread_H
imports
  ThreadDecls_H
  CSpace_H
  ArchThread_H
  FaultHandler_H
  Config_H
begin

arch_requalify_consts (H)
  capRegister
  faultRegister
  nextInstructionRegister

context Arch begin

(* match Haskell, expects these under Arch. *)
requalify_consts
  activateIdleThread

(* disambiguate name clash between Arch and non-arch consts with same names *)
requalify_consts (aliasing)
  configureIdleThread
  switchToIdleThread
  switchToThread
  prepareNextDomain

context begin global_naming global

requalify_consts (aliasing)
  ThreadDecls_H.configureIdleThread
  ThreadDecls_H.switchToIdleThread
  ThreadDecls_H.switchToThread

end
end

#INCLUDE_HASKELL SEL4/Kernel/Thread.lhs Arch=Arch bodies_only NOT doNormalTransfer doIPCTransfer doReplyTransfer doNormalTransfer transferCaps transferCapsToSlots

#INCLUDE_HASKELL SEL4/Kernel/Thread.lhs Arch=Arch ONLY transferCapsToSlots

#INCLUDE_HASKELL SEL4/Kernel/Thread.lhs Arch=Arch bodies_only ONLY doNormalTransfer doIPCTransfer doReplyTransfer doNormalTransfer transferCaps

end
