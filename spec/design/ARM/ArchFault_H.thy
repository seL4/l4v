(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchFault_H.thy *)
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
  VSpace lookup code.
*)

theory ArchFault_H
imports "../Types_H"
begin
context Arch begin global_naming ARM_H


datatype arch_fault =
    VMFault vptr "machine_word list"

primrec
  vmFaultAddress :: "arch_fault \<Rightarrow> vptr"
where
  "vmFaultAddress (VMFault v0 v1) = v0"

primrec
  vmFaultArchData :: "arch_fault \<Rightarrow> machine_word list"
where
  "vmFaultArchData (VMFault v0 v1) = v1"

primrec
  vmFaultAddress_update :: "(vptr \<Rightarrow> vptr) \<Rightarrow> arch_fault \<Rightarrow> arch_fault"
where
  "vmFaultAddress_update f (VMFault v0 v1) = VMFault (f v0) v1"

primrec
  vmFaultArchData_update :: "((machine_word list) \<Rightarrow> (machine_word list)) \<Rightarrow> arch_fault \<Rightarrow> arch_fault"
where
  "vmFaultArchData_update f (VMFault v0 v1) = VMFault v0 (f v1)"

abbreviation (input)
  VMFault_trans :: "(vptr) \<Rightarrow> (machine_word list) \<Rightarrow> arch_fault" ("VMFault'_ \<lparr> vmFaultAddress= _, vmFaultArchData= _ \<rparr>")
where
  "VMFault_ \<lparr> vmFaultAddress= v0, vmFaultArchData= v1 \<rparr> == VMFault v0 v1"

lemma vmFaultAddress_vmFaultAddress_update [simp]:
  "vmFaultAddress (vmFaultAddress_update f v) = f (vmFaultAddress v)"
  by (cases v) simp

lemma vmFaultAddress_vmFaultArchData_update [simp]:
  "vmFaultAddress (vmFaultArchData_update f v) = vmFaultAddress v"
  by (cases v) simp

lemma vmFaultArchData_vmFaultAddress_update [simp]:
  "vmFaultArchData (vmFaultAddress_update f v) = vmFaultArchData v"
  by (cases v) simp

lemma vmFaultArchData_vmFaultArchData_update [simp]:
  "vmFaultArchData (vmFaultArchData_update f v) = f (vmFaultArchData v)"
  by (cases v) simp



end
end
