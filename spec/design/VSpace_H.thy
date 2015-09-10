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
"initKernelVM \<equiv> ArchVSpaceDecls_H.mapKernelWindow"

definition
initPlatform :: "unit kernel"
where
"initPlatform\<equiv> (do
  doMachineOp $ configureTimer;
  doMachineOp $ initL2Cache
od)"

definition
initCPU :: "unit kernel"
where
"initCPU \<equiv> ArchVSpaceDecls_H.activateGlobalPD"

definition
createIPCBufferFrame :: "capability \<Rightarrow> vptr \<Rightarrow> capability kernel_init"
where
"createIPCBufferFrame  \<equiv> ArchVSpaceDecls_H.createIPCBufferFrame"

definition
createBIFrame :: "capability \<Rightarrow> vptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> capability kernel_init"
where
"createBIFrame  \<equiv> ArchVSpaceDecls_H.createBIFrame"

definition
createFramesOfRegion :: "capability \<Rightarrow> region \<Rightarrow> bool \<Rightarrow> vptr \<Rightarrow> unit kernel_init"
where
"createFramesOfRegion \<equiv> ArchVSpaceDecls_H.createFramesOfRegion"

definition
createITPDPTs :: "capability \<Rightarrow> vptr \<Rightarrow> vptr \<Rightarrow> capability kernel_init"
where
"createITPDPTs \<equiv> ArchVSpaceDecls_H.createITPDPTs"

definition
writeITPDPTs :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel_init"
where
"writeITPDPTs \<equiv> ArchVSpaceDecls_H.writeITPDPTs"

definition
createITASIDPool :: "capability \<Rightarrow> capability kernel_init"
where
"createITASIDPool \<equiv> ArchVSpaceDecls_H.createITASIDPool"

definition
writeITASIDPool :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel"
where
"writeITASIDPool \<equiv> ArchVSpaceDecls_H.writeITASIDPool"

definition
createDeviceFrames :: "capability \<Rightarrow> unit kernel_init"
where
"createDeviceFrames \<equiv> ArchVSpaceDecls_H.createDeviceFrames"

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


end
