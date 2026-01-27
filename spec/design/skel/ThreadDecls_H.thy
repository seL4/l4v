(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Function Declarations for Threads"

theory ThreadDecls_H
imports
  Structures_H
  FaultMonad_H
  KernelInitMonad_H
  ArchThreadDecls_H
begin

#INCLUDE_HASKELL SEL4/Kernel/Thread.lhs decls_only NOT transferCapsToSlots tcbQueueEmpty

end
