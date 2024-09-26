(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchStructures_H
imports
  "Lib.Lib"
  Types_H
  Hardware_H
begin
context Arch begin arch_global_naming (H)

#INCLUDE_SETTINGS keep_constructor=asidpool
#INCLUDE_SETTINGS keep_constructor=arch_tcb

#INCLUDE_HASKELL SEL4/Object/Structures/ARM.lhs CONTEXT ARM_H decls_only \
  NOT ArchTcbFlag archTcbFlagToWord
#INCLUDE_HASKELL SEL4/Object/Structures/ARM.lhs CONTEXT ARM_H instanceproofs
#INCLUDE_HASKELL SEL4/Object/Structures/ARM.lhs CONTEXT ARM_H bodies_only \
  NOT archTcbFlagToWord

datatype arch_kernel_object_type =
    PDET
  | PTET
  | ASIDPoolT

primrec
  archTypeOf :: "arch_kernel_object \<Rightarrow> arch_kernel_object_type"
where
  "archTypeOf (KOPDE e) = PDET"
| "archTypeOf (KOPTE e) = PTET"
| "archTypeOf (KOASIDPool e) = ASIDPoolT"

end
end
