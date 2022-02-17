(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Declarations from SEL4.Kernel.Thread.
*)

chapter "Function Declarations for Threads"

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchThreadDecls_H
imports
  Structures_H
  FaultMonad_H
  KernelInitMonad_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/Kernel/Thread/AARCH64.hs CONTEXT AARCH64_H decls_only

end (* context AARCH64 *)

end
