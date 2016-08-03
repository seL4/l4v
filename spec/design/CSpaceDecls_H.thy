(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file CSpaceDecls_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Function Declarations for CSpace"

theory CSpaceDecls_H
imports FaultMonad_H
begin

consts'
lookupCap :: "machine_word \<Rightarrow> cptr \<Rightarrow> ( lookup_failure , capability ) kernel_f"

consts'
lookupCapAndSlot :: "machine_word \<Rightarrow> cptr \<Rightarrow> ( lookup_failure , (capability * machine_word) ) kernel_f"

consts'
lookupSlotForThread :: "machine_word \<Rightarrow> cptr \<Rightarrow> ( lookup_failure , (machine_word) ) kernel_f"

consts'
lookupSlotForCNodeOp :: "bool \<Rightarrow> capability \<Rightarrow> cptr \<Rightarrow> nat \<Rightarrow> ( syscall_error , (machine_word) ) kernel_f"

consts'
lookupSourceSlot :: "capability \<Rightarrow> cptr \<Rightarrow> nat \<Rightarrow> ( syscall_error , (machine_word) ) kernel_f"

consts'
lookupTargetSlot :: "capability \<Rightarrow> cptr \<Rightarrow> nat \<Rightarrow> ( syscall_error , (machine_word) ) kernel_f"

consts'
lookupPivotSlot :: "capability \<Rightarrow> cptr \<Rightarrow> nat \<Rightarrow> ( syscall_error , (machine_word) ) kernel_f"

consts'
resolveAddressBits :: "capability \<Rightarrow> cptr \<Rightarrow> nat \<Rightarrow> ( lookup_failure , (machine_word * nat) ) kernel_f"


end
