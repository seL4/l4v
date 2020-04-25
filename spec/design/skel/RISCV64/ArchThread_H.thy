(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Threads"

theory ArchThread_H
imports
  ArchThreadDecls_H
  "../TCBDecls_H"
  ArchVSpaceDecls_H
begin


context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/Kernel/Thread/RISCV64.hs CONTEXT RISCV64_H Arch=MachineOps ArchReg=MachineTypes bodies_only

end (* context RISCV64 *)

end
