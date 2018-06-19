(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
