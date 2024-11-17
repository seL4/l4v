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
context Arch begin arch_global_naming (H)

definition
  Word :: "machine_word \<Rightarrow> machine_word"
where
  Word_def[simp]:
 "Word \<equiv> id"

#INCLUDE_HASKELL Data/WordLib.lhs all_bits ONLY wordBits

end

(* Note: while this requalify and arch-generic Haskell import of WordLib.lhs could be moved to
   a generic theory, no good candidate theory exists at the moment. *)
arch_requalify_consts (H)
  wordBits

#INCLUDE_HASKELL Data/WordLib.lhs all_bits NOT wordBits

context Arch begin arch_global_naming (H)

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
