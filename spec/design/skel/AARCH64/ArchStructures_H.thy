(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchStructures_H
imports
  "Lib.Lib"
  Types_H
  Hardware_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_SETTINGS keep_constructor=asidpool
#INCLUDE_SETTINGS keep_constructor=arch_tcb

#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64_H decls_only
#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64_H instanceproofs
#INCLUDE_HASKELL SEL4/Object/Structures/AARCH64.hs CONTEXT AARCH64_H bodies_only

datatype arch_kernel_object_type =
    PTET
  | ASIDPoolT

primrec
  archTypeOf :: "arch_kernel_object \<Rightarrow> arch_kernel_object_type"
where
  "archTypeOf (KOPTE e) = PTET"
| "archTypeOf (KOASIDPool e) = ASIDPoolT"

end
end
