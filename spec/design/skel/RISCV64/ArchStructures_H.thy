(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchStructures_H
imports
  "Lib.Lib"
  "../Types_H"
  Hardware_H
begin

context Arch begin global_naming RISCV64_H

#INCLUDE_SETTINGS keep_constructor=asidpool
#INCLUDE_SETTINGS keep_constructor=arch_tcb

#INCLUDE_HASKELL SEL4/Object/Structures/RISCV64.hs CONTEXT RISCV64_H decls_only
#INCLUDE_HASKELL SEL4/Object/Structures/RISCV64.hs CONTEXT RISCV64_H instanceproofs
#INCLUDE_HASKELL SEL4/Object/Structures/RISCV64.hs CONTEXT RISCV64_H bodies_only

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
