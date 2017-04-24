(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchVSpaceDecls_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Retyping Objects"

theory ArchVSpaceDecls_H
imports ArchRetypeDecls_H "../InvocationLabels_H"
begin

context Arch begin global_naming X64_H

consts'
kernelBase :: "vptr"

consts'
globalsBase :: "vptr"

consts'
idleThreadStart :: "vptr"

consts'
copyGlobalMappings :: "machine_word \<Rightarrow> unit kernel"

consts'
createMappingEntries :: "paddr \<Rightarrow> vptr \<Rightarrow> vmpage_size \<Rightarrow> vmrights \<Rightarrow> vmattributes \<Rightarrow> machine_word \<Rightarrow> ( syscall_error , (vmpage_entry * vmpage_entry_ptr) ) kernel_f"

consts'
ensureSafeMapping :: "(vmpage_entry * vmpage_entry_ptr) \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts'
lookupIPCBuffer :: "bool \<Rightarrow> machine_word \<Rightarrow> ((machine_word) option) kernel"

consts'
findVSpaceForASID :: "asid \<Rightarrow> ( lookup_failure , (machine_word) ) kernel_f"

consts'
findVSpaceForASIDAssert :: "asid \<Rightarrow> (machine_word) kernel"

consts'
checkPML4At :: "machine_word \<Rightarrow> unit kernel"

consts'
checkPDPTAt :: "machine_word \<Rightarrow> unit kernel"

consts'
checkPDAt :: "machine_word \<Rightarrow> unit kernel"

consts'
checkPTAt :: "machine_word \<Rightarrow> unit kernel"

consts'
checkPML4ASIDMapMembership :: "machine_word \<Rightarrow> asid list \<Rightarrow> unit kernel"

consts'
checkPML4UniqueToASID :: "machine_word \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
checkPML4NotInASIDMap :: "machine_word \<Rightarrow> unit kernel"

consts'
lookupPTSlot :: "machine_word \<Rightarrow> vptr \<Rightarrow> ( lookup_failure , (machine_word) ) kernel_f"

consts'
lookupPTSlotFromPT :: "machine_word \<Rightarrow> vptr \<Rightarrow> (machine_word) kernel"

consts'
lookupPDSlot :: "machine_word \<Rightarrow> vptr \<Rightarrow> ( lookup_failure , (machine_word) ) kernel_f"

consts'
lookupPDSlotFromPD :: "machine_word \<Rightarrow> vptr \<Rightarrow> (machine_word) kernel"

consts'
lookupPDPTSlot :: "machine_word \<Rightarrow> vptr \<Rightarrow> ( lookup_failure , (machine_word) ) kernel_f"

consts'
lookupPDPTSlotFromPDPT :: "machine_word \<Rightarrow> vptr \<Rightarrow> (machine_word) kernel"

consts'
lookupPML4Slot :: "machine_word \<Rightarrow> vptr \<Rightarrow> machine_word"

consts'
handleVMFault :: "machine_word \<Rightarrow> vmfault_type \<Rightarrow> ( fault , unit ) kernel_f"

consts'
deleteASIDPool :: "asid \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
deleteASID :: "asid \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
unmapPDPT :: "asid \<Rightarrow> vptr \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
unmapPageDirectory :: "asid \<Rightarrow> vptr \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
unmapPageTable :: "asid \<Rightarrow> vptr \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
unmapPage :: "vmpage_size \<Rightarrow> asid \<Rightarrow> vptr \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
checkMappingPPtr :: "machine_word \<Rightarrow> vmpage_entry \<Rightarrow> ( lookup_failure , unit ) kernel_f"

consts'
getCurrentCR3 :: "cr3 kernel"

consts'
setCurrentCR3 :: "cr3 \<Rightarrow> unit kernel"

consts'
invalidateLocalPageStructureCacheASID :: "paddr \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
invalidatePageStructureCacheASID :: "paddr \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
getCurrentVSpaceRoot :: "paddr kernel"

consts'
setCurrentVSpaceRoot :: "paddr \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
updateASIDMap :: "asid \<Rightarrow> unit kernel"

consts'
setVMRoot :: "machine_word \<Rightarrow> unit kernel"

consts'
isValidVTableRoot :: "capability \<Rightarrow> bool"

consts'
checkValidIPCBuffer :: "vptr \<Rightarrow> capability \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts'
maskVMRights :: "vmrights \<Rightarrow> cap_rights \<Rightarrow> vmrights"

consts'
flushAll :: "machine_word \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
flushPDPT  :: "machine_word \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
flushPD :: "machine_word \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
flushTable :: "machine_word \<Rightarrow> vptr \<Rightarrow> machine_word \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
invalidateASID' :: "asid \<Rightarrow> unit kernel"

consts'
invalidateASIDEntry :: "asid \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
attribsFromWord :: "machine_word \<Rightarrow> vmattributes"

consts'
pageBase :: "vptr \<Rightarrow> vmpage_size \<Rightarrow> vptr"

consts'
userVTop :: "machine_word"

consts'
decodeX64FrameInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
decodeX64PDPointerTableInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
decodeX64PageDirectoryInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
decodeX64PageTableInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
decodeX64ASIDControlInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
decodeX64ASIDPoolInvocation :: "machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
decodeX64MMUInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> cptr \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
checkVPAlignment :: "vmpage_size \<Rightarrow> vptr \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts'
checkValidMappingSize :: "vmpage_size \<Rightarrow> unit kernel"

consts'
performX64MMUInvocation :: "invocation \<Rightarrow> machine_word list kernel_p"

consts'
performPDPTInvocation :: "pdptinvocation \<Rightarrow> unit kernel"

consts'
performPageDirectoryInvocation :: "page_directory_invocation \<Rightarrow> unit kernel"

consts'
performPageTableInvocation :: "page_table_invocation \<Rightarrow> unit kernel"

consts'
pteCheckIfMapped :: "machine_word \<Rightarrow> bool kernel"

consts'
pdeCheckIfMapped :: "machine_word \<Rightarrow> bool kernel"

consts'
performPageInvocation :: "page_invocation \<Rightarrow> unit kernel"

consts'
performASIDControlInvocation :: "asidcontrol_invocation \<Rightarrow> unit kernel"

consts'
performASIDPoolInvocation :: "asidpool_invocation \<Rightarrow> unit kernel"

consts'
storePML4E :: "machine_word \<Rightarrow> pml4e \<Rightarrow> unit kernel"

consts'
storePDPTE :: "machine_word \<Rightarrow> pdpte \<Rightarrow> unit kernel"

consts'
storePDE :: "machine_word \<Rightarrow> pde \<Rightarrow> unit kernel"

consts'
storePTE :: "machine_word \<Rightarrow> pte \<Rightarrow> unit kernel"

consts'
mapKernelWindow  :: "unit kernel"

consts'
activateGlobalVSpace :: "unit kernel"

consts'
createIPCBufferFrame :: "capability \<Rightarrow> vptr \<Rightarrow> capability kernel_init"

consts'
createBIFrame :: "capability \<Rightarrow> vptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> capability kernel_init"

consts'
createFramesOfRegion :: "capability \<Rightarrow> region \<Rightarrow> bool \<Rightarrow> unit kernel_init"

consts'
createITPDPTs :: "capability \<Rightarrow> vptr \<Rightarrow> vptr \<Rightarrow> capability kernel_init"

consts'
writeITPDPTs :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel_init"

consts'
createITASIDPool :: "capability \<Rightarrow> capability kernel_init"

consts'
writeITASIDPool :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel"

consts'
createDeviceFrames :: "capability \<Rightarrow> unit kernel_init"

consts'
vptrFromPPtr :: "machine_word \<Rightarrow> vptr kernel_init"

consts'
ensurePortOperationAllowed :: "arch_capability \<Rightarrow> ioport \<Rightarrow> nat \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts'
decodeX64PortInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> arch_capability \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
performX64PortInvocation :: "invocation \<Rightarrow> machine_word list kernel_p"


end (* context X64 *)

end
