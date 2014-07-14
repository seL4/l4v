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

theory VSpace_H
imports
  CNode_H
  ArchVSpace_H
  KernelInitMonad_H
begin

definition
initKernelVM :: "unit kernel"
where
"initKernelVM \<equiv> ArchVSpaceDecls_H.initKernelVM"

definition
initVSpace :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel_init"
where
"initVSpace \<equiv> ArchVSpaceDecls_H.initVSpace"

definition
handleVMFault :: "machine_word \<Rightarrow> vmfault_type \<Rightarrow> ( fault , unit ) kernel_f"
where
"handleVMFault \<equiv> ArchVSpaceDecls_H.handleVMFault"

definition
isValidVTableRoot :: "capability \<Rightarrow> bool"
where
"isValidVTableRoot \<equiv> ArchVSpaceDecls_H.isValidVTableRoot"

definition
checkValidIPCBuffer :: "vptr \<Rightarrow> capability \<Rightarrow> ( syscall_error , unit ) kernel_f"
where
"checkValidIPCBuffer \<equiv> ArchVSpaceDecls_H.checkValidIPCBuffer"

definition
lookupIPCBuffer :: "bool \<Rightarrow> machine_word \<Rightarrow> ((machine_word) option) kernel"
where
"lookupIPCBuffer \<equiv> ArchVSpaceDecls_H.lookupIPCBuffer"

definition
createInitPage :: "paddr \<Rightarrow> capability kernel"
where
"createInitPage \<equiv> ArchVSpaceDecls_H.createInitPage"

definition
createDeviceCap :: "(paddr * paddr) \<Rightarrow> capability kernel"
where
"createDeviceCap \<equiv> ArchVSpaceDecls_H.createDeviceCap"


end
