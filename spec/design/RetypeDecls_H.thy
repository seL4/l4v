(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file RetypeDecls_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Function Declarations for Retyping Objects"

theory RetypeDecls_H
imports
  "./$L4V_ARCH/ArchRetypeDecls_H"
  Structures_H
  FaultMonad_H
  Invocations_H
begin

consts'
deriveCap :: "machine_word \<Rightarrow> capability \<Rightarrow> ( syscall_error , capability ) kernel_f"

consts'
finaliseCap :: "capability \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (capability * irq option) kernel"

consts'
hasCancelSendRights :: "capability \<Rightarrow> bool"

consts'
sameRegionAs :: "capability \<Rightarrow> capability \<Rightarrow> bool"

consts'
isPhysicalCap :: "capability \<Rightarrow> bool"

consts'
sameObjectAs :: "capability \<Rightarrow> capability \<Rightarrow> bool"

consts'
updateCapData :: "bool \<Rightarrow> machine_word \<Rightarrow> capability \<Rightarrow> capability"

consts'
badgeBits :: "nat"

consts'
maskCapRights :: "cap_rights \<Rightarrow> capability \<Rightarrow> capability"

consts'
createObject :: "object_type \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> capability kernel"

consts'
decodeInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> cptr \<Rightarrow> machine_word \<Rightarrow> capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
performInvocation :: "bool \<Rightarrow> bool \<Rightarrow> invocation \<Rightarrow> machine_word list kernel_p"

consts'
capUntypedPtr :: "capability \<Rightarrow> machine_word"

consts'
capUntypedSize :: "capability \<Rightarrow> machine_word"


consts'
deletedIRQHandler :: "irq \<Rightarrow> unit kernel"


end
