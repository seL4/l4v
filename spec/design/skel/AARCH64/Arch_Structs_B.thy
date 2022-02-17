(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Architecture-specific data types shared by spec and abstract. *)

chapter "Common, Architecture-Specific Data Types"

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory Arch_Structs_B
imports Setup_Locale
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/Model/StateData/AARCH64.hs CONTEXT AARCH64_H ONLY RISCVVSpaceRegionUse

end

end
