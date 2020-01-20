(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* Architecture-specific data types shared by spec and abstract. *)

chapter "Common, Architecture-Specific Data Types"

theory Arch_Structs_B
imports "../../../spec/machine/Setup_Locale"
begin

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/Model/StateData/RISCV64.hs CONTEXT RISCV64_H ONLY RISCVVSpaceRegionUse

end

end
