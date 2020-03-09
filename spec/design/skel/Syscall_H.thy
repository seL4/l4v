(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "System Calls"

theory Syscall_H
imports Kernel_H Event_H
begin

#INCLUDE_HASKELL SEL4/Model/Syscall.lhs
#INCLUDE_HASKELL SEL4/API/Syscall.lhs decls_only NOT Event Syscall
#INCLUDE_HASKELL SEL4/API/Syscall.lhs bodies_only

end
