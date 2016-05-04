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

type_synonym register = "ARM.register"

definition
  Register :: "register \<Rightarrow> register"
where Register_def[simp]:
 "Register \<equiv> id"

type_synonym vptr = "machine_word"

definition
  VPtr :: "vptr \<Rightarrow> vptr"
where VPtr_def[simp]:
 "VPtr \<equiv> id"

definition
  fromVPtr :: "vptr \<Rightarrow> vptr"
where
  fromVPtr_def[simp]:
 "fromVPtr \<equiv> id"

definition  fromVPtr_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> vptr \<Rightarrow> vptr"
where
  fromVPtr_update_def[simp]:
 "fromVPtr_update f y \<equiv> f y"

abbreviation (input)
  VPtr_trans :: "(machine_word) \<Rightarrow> vptr" ("VPtr'_ \<lparr> fromVPtr= _ \<rparr>")
where
  "VPtr_ \<lparr> fromVPtr= v0 \<rparr> == VPtr v0"

definition
msgInfoRegister :: "register"
where
"msgInfoRegister \<equiv> Register ARM.msgInfoRegister"

definition
msgRegisters :: "register list"
where
"msgRegisters \<equiv> map Register ARM.msgRegisters"

definition
capRegister :: "register"
where
"capRegister \<equiv> Register ARM.capRegister"

definition
badgeRegister :: "register"
where
"badgeRegister \<equiv> Register ARM.badgeRegister"

definition
frameRegisters :: "register list"
where
"frameRegisters \<equiv> map Register ARM.frameRegisters"

definition
gpRegisters :: "register list"
where
"gpRegisters \<equiv> map Register ARM.gpRegisters"

definition
exceptionMessage :: "register list"
where
"exceptionMessage \<equiv> map Register ARM.exceptionMessage"

definition
syscallMessage :: "register list"
where
"syscallMessage \<equiv> map Register ARM.syscallMessage"

definition
sanitiseRegister :: "register \<Rightarrow> machine_word \<Rightarrow> machine_word"
where
"sanitiseRegister x0 x1\<equiv> (case (x0, x1) of
    (((* Register *) r), ((* Word *) w)) \<Rightarrow>    Word $ ARM.sanitiseRegister r w
  )"


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
