(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating;
   update copyright as necessary. *)
theory ArchCrunchSetup_AI
imports
  "ASpec.Syscall_A"
  "Lib.Crunch_Instances_NonDet"
begin

context Arch begin global_naming AARCH64

crunch_ignore (add: debugPrint clearMemory pt_lookup_from_level)

end

end
