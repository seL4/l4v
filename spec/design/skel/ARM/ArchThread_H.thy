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

#INCLUDE_HASKELL SEL4/Kernel/Thread/ARM.lhs CONTEXT ARM_H ARMHardware=ARM bodies_only

end
end
