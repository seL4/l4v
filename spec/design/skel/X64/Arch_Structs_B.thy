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
imports "~~/src/HOL/Main" "../../../spec/machine/Setup_Locale"
begin
(* FIXME: Clagged from X64 version *)

context Arch begin global_naming X64_H

(* FIXME: add an underscore after translation of X64 prefix? *)
#INCLUDE_HASKELL SEL4/Model/StateData/X64.lhs CONTEXT X64_H ONLY X64VSpaceRegionUse

end (* context X64 *)

end
