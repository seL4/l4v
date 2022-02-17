(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Threads"

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchThread_H
imports
  ArchThreadDecls_H
  TCBDecls_H
  ArchVSpaceDecls_H
  ArchHypervisor_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/Kernel/Thread/AARCH64.hs CONTEXT AARCH64_H Arch=MachineOps ArchReg=MachineTypes bodies_only

end (* context AARCH64 *)

end
