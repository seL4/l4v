(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
	Machine and kernel state.
*)

chapter "Machine State"

theory State_H
imports
  "../../../lib/HaskellLib_H"
  RegisterSet_H
  "../../machine/ARM/MachineOps"
begin
context Arch begin global_naming ARM_H

definition
  Word :: "machine_word \<Rightarrow> machine_word"
where
  Word_def[simp]:
 "Word \<equiv> id"

#INCLUDE_HASKELL SEL4/Machine/RegisterSet.lhs Arch=ARM CONTEXT ARM_H all_bits NOT UserContext UserMonad getRegister setRegister newContext mask Word PPtr

definition
  PPtr :: "machine_word \<Rightarrow> machine_word"
where
  PPtr_def[simp]:
 "PPtr \<equiv> id"

definition
  fromPPtr :: "machine_word \<Rightarrow> machine_word"
where
  fromPPtr_def[simp]:
 "fromPPtr \<equiv> id"

definition
  nullPointer :: machine_word
where
 "nullPointer \<equiv> 0"

end
end
