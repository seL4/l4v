(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Machine and kernel state.
*)

chapter "Machine State"

theory State_H
imports
  "Lib.HaskellLib_H"
  RegisterSet_H
  MachineOps
begin
context Arch begin global_naming ARM_HYP_H

definition
  Word :: "machine_word \<Rightarrow> machine_word"
where
  Word_def[simp]:
 "Word \<equiv> id"

#INCLUDE_HASKELL Data/WordLib.lhs all_bits ONLY wordBits

end

context begin interpretation Arch .

requalify_consts
  wordBits

end

#INCLUDE_HASKELL Data/WordLib.lhs all_bits NOT wordBits

context Arch begin global_naming ARM_HYP_H


#INCLUDE_HASKELL SEL4/Machine/RegisterSet.lhs Arch=ARM_HYP CONTEXT ARM_HYP_H all_bits NOT UserContext UserMonad getRegister setRegister newContext mask Word PPtr

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
