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
	Kernel state and kernel monads, imports everything that SEL4.Model needs.
*)

chapter "Architecture Specific Kernel State and Monads"

theory ArchStateData_H
imports
  Arch_Structs_B
  ArchTypes_H
  ArchStructures_H
begin

context X64 begin

datatype kernel_state =
    X64KernelState machine_word "asid \<Rightarrow> ((machine_word) option)" machine_word

primrec
  x64KSASIDTable :: "kernel_state \<Rightarrow> asid \<Rightarrow> ((machine_word) option)"
where
  "x64KSASIDTable (X64KernelState v0 v1 v2) = v1"

primrec
  x64KSGlobalPML4 :: "kernel_state \<Rightarrow> machine_word"
where
  "x64KSGlobalPML4 (X64KernelState v0 v1 v2) = v2"

primrec
  x64KSGDT :: "kernel_state \<Rightarrow> machine_word"
where
  "x64KSGDT (X64KernelState v0 v1 v2) = v0"

primrec
  x64KSASIDTable_update :: "((asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (asid \<Rightarrow> ((machine_word) option))) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "x64KSASIDTable_update f (X64KernelState v0 v1 v2) = X64KernelState v0 (f v1) v2"

primrec
  x64KSGlobalPML4_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "x64KSGlobalPML4_update f (X64KernelState v0 v1 v2) = X64KernelState v0 v1 (f v2)"

primrec
  x64KSGDT_update :: "(machine_word \<Rightarrow> machine_word) \<Rightarrow> kernel_state \<Rightarrow> kernel_state"
where
  "x64KSGDT_update f (X64KernelState v0 v1 v2) = X64KernelState (f v0) v1 v2"

abbreviation (input)
  X64KernelState_trans :: "(machine_word) \<Rightarrow> (asid \<Rightarrow> ((machine_word) option)) \<Rightarrow> (machine_word) \<Rightarrow> kernel_state" ("X64KernelState'_ \<lparr> x64KSGDT= _, x64KSASIDTable= _, x64KSGlobalPML4= _ \<rparr>")
where
  "X64KernelState_ \<lparr> x64KSGDT= v0, x64KSASIDTable= v1, x64KSGlobalPML4= v2 \<rparr> == X64KernelState v0 v1 v2"

lemma x64KSASIDTable_x64KSASIDTable_update [simp]:
  "x64KSASIDTable (x64KSASIDTable_update f v) = f (x64KSASIDTable v)"
  by (cases v) simp

lemma x64KSASIDTable_x64KSGlobalPML4_update [simp]:
  "x64KSASIDTable (x64KSGlobalPML4_update f v) = x64KSASIDTable v"
  by (cases v) simp

lemma x64KSASIDTable_x64KSGDT_update [simp]:
  "x64KSASIDTable (x64KSGDT_update f v) = x64KSASIDTable v"
  by (cases v) simp

lemma x64KSGlobalPML4_x64KSASIDTable_update [simp]:
  "x64KSGlobalPML4 (x64KSASIDTable_update f v) = x64KSGlobalPML4 v"
  by (cases v) simp

lemma x64KSGlobalPML4_x64KSGlobalPML4_update [simp]:
  "x64KSGlobalPML4 (x64KSGlobalPML4_update f v) = f (x64KSGlobalPML4 v)"
  by (cases v) simp

lemma x64KSGlobalPML4_x64KSGDT_update [simp]:
  "x64KSGlobalPML4 (x64KSGDT_update f v) = x64KSGlobalPML4 v"
  by (cases v) simp

lemma x64KSGDT_x64KSASIDTable_update [simp]:
  "x64KSGDT (x64KSASIDTable_update f v) = x64KSGDT v"
  by (cases v) simp

lemma x64KSGDT_x64KSGlobalPML4_update [simp]:
  "x64KSGDT (x64KSGlobalPML4_update f v) = x64KSGDT v"
  by (cases v) simp

lemma x64KSGDT_x64KSGDT_update [simp]:
  "x64KSGDT (x64KSGDT_update f v) = f (x64KSGDT v)"
  by (cases v) simp

definition
gdteBits :: "nat"
where
"gdteBits \<equiv> 3"

definition
newKernelState :: "paddr \<Rightarrow> (kernel_state * paddr list)"
where
"newKernelState arg1 \<equiv> error []"


end
end
