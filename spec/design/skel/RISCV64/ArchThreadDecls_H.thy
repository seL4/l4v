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

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Kernel/Thread/RISCV64.hs CONTEXT RISCV64_H decls_only

end (* context RISCV64 *)

end
