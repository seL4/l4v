(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Threads"

theory ArchThread_H
imports
  ArchThreadDecls_H
  TCBDecls_H
  ArchVSpaceDecls_H
begin


context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Kernel/Thread/X64.lhs CONTEXT X64_H Arch=MachineOps ArchReg=MachineTypes bodies_only

end (* context X64 *)

end
