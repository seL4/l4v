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


context Arch begin global_naming X64_H

#INCLUDE_HASKELL SEL4/Kernel/Thread/X64.lhs CONTEXT X64_H Arch=MachineOps ArchReg=MachineTypes bodies_only

end (* context X64 *)

end
