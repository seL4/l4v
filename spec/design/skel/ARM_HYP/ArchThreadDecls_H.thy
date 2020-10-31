(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Declarations from SEL4.Kernel.Thread.
*)

chapter "Function Declarations for Threads"

theory ArchThreadDecls_H
imports
  Structures_H
  FaultMonad_H
  KernelInitMonad_H
begin

context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Kernel/Thread/ARM.lhs CONTEXT Arch decls_only

end
end
