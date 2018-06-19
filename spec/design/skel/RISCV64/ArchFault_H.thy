(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
  VSpace lookup code.
*)

theory ArchFault_H
imports "../Types_H"
begin

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/API/Failures/RISCV64.hs CONTEXT RISCV64_H decls_only
#INCLUDE_HASKELL SEL4/API/Failures/RISCV64.hs CONTEXT RISCV64_H bodies_only

end
end
