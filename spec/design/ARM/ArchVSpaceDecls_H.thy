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
context Arch begin global_naming ARM_H

consts'
globalsBase :: "vptr"

consts'
idleThreadStart :: "vptr"

consts'
idleThreadCode :: "machine_word list"

consts'
mapKernelWindow :: "unit kernel"

consts'
createSectionPDE :: "vptr \<Rightarrow> unit kernel"

consts'
mapKernelDevice :: "(paddr * machine_word) \<Rightarrow> unit kernel"

consts'
activateGlobalVSpace :: "unit kernel"

consts'
createITPDPTs :: "capability \<Rightarrow> vptr \<Rightarrow> vptr \<Rightarrow> capability kernel_init"

consts'
writeITPDPTs :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel_init"

consts'
createITASIDPool :: "capability \<Rightarrow> capability kernel_init"

consts'
writeITASIDPool :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel"

consts'
mapITPTCap :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel"

consts'
mapITFrameCap :: "capability \<Rightarrow> capability \<Rightarrow> unit kernel"

consts'
createIPCBufferFrame :: "capability \<Rightarrow> vptr \<Rightarrow> capability kernel_init"

consts'
createBIFrame :: "capability \<Rightarrow> vptr \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> capability kernel_init"

consts'
createITFrameCap :: "machine_word \<Rightarrow> vptr \<Rightarrow> asid option \<Rightarrow> bool \<Rightarrow> capability kernel_init"

consts'
vptrFromPPtr :: "machine_word \<Rightarrow> vptr kernel_init"

consts'
createFramesOfRegion :: "capability \<Rightarrow> region \<Rightarrow> bool \<Rightarrow> unit kernel_init"

consts'
mapGlobalsFrame :: "unit kernel"

consts'
writeIdleCode :: "unit kernel"

consts'
mapKernelFrame :: "paddr \<Rightarrow> vptr \<Rightarrow> vmrights \<Rightarrow> vmattributes \<Rightarrow> unit kernel"

consts'
getARMGlobalPT :: "(machine_word) kernel"

consts'
createDeviceFrames :: "capability \<Rightarrow> unit kernel_init"

consts'
copyGlobalMappings :: "machine_word \<Rightarrow> unit kernel"

consts'
createMappingEntries :: "paddr \<Rightarrow> vptr \<Rightarrow> vmpage_size \<Rightarrow> vmrights \<Rightarrow> vmattributes \<Rightarrow> machine_word \<Rightarrow> ( syscall_error , ((pte * machine_word list) + (pde * machine_word list)) ) kernel_f"

consts'
ensureSafeMapping :: "(pte * machine_word list) + (pde * machine_word list) \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts'
lookupIPCBuffer :: "bool \<Rightarrow> machine_word \<Rightarrow> ((machine_word) option) kernel"

consts'
findPDForASID :: "asid \<Rightarrow> ( lookup_failure , (machine_word) ) kernel_f"

consts'
findPDForASIDAssert :: "asid \<Rightarrow> (machine_word) kernel"

consts'
checkPDAt :: "machine_word \<Rightarrow> unit kernel"

consts'
checkPTAt :: "machine_word \<Rightarrow> unit kernel"

consts'
checkPDASIDMapMembership :: "machine_word \<Rightarrow> asid list \<Rightarrow> unit kernel"

consts'
checkPDUniqueToASID :: "machine_word \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
checkPDNotInASIDMap :: "machine_word \<Rightarrow> unit kernel"

consts'
lookupPTSlot :: "machine_word \<Rightarrow> vptr \<Rightarrow> ( lookup_failure , (machine_word) ) kernel_f"

consts'
lookupPTSlotFromPT :: "machine_word \<Rightarrow> vptr \<Rightarrow> (machine_word) kernel"

consts'
lookupPDSlot :: "machine_word \<Rightarrow> vptr \<Rightarrow> machine_word"

consts'
handleVMFault :: "machine_word \<Rightarrow> vmfault_type \<Rightarrow> ( fault , unit ) kernel_f"

consts'
deleteASIDPool :: "asid \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
deleteASID :: "asid \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
pageTableMapped :: "asid \<Rightarrow> vptr \<Rightarrow> machine_word \<Rightarrow> ((machine_word) option) kernel"

consts'
unmapPageTable :: "asid \<Rightarrow> vptr \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
unmapPage :: "vmpage_size \<Rightarrow> asid \<Rightarrow> vptr \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts'
checkMappingPPtr :: "machine_word \<Rightarrow> vmpage_size \<Rightarrow> (machine_word) + (machine_word) \<Rightarrow> ( lookup_failure , unit ) kernel_f"

consts'
armv_contextSwitch_HWASID :: "machine_word \<Rightarrow> hardware_asid \<Rightarrow> unit machine_monad"

consts'
armv_contextSwitch :: "machine_word \<Rightarrow> asid \<Rightarrow> unit kernel"

consts'
setVMRoot :: "machine_word \<Rightarrow> unit kernel"

consts'
setVMRootForFlush :: "machine_word \<Rightarrow> asid \<Rightarrow> bool kernel"

consts'
isValidVTableRoot :: "capability \<Rightarrow> bool"

consts'
checkValidIPCBuffer :: "vptr \<Rightarrow> capability \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts'
maskVMRights :: "vmrights \<Rightarrow> cap_rights \<Rightarrow> vmrights"

consts'
attribsFromWord :: "machine_word \<Rightarrow> vmattributes"

consts'
storeHWASID :: "asid \<Rightarrow> hardware_asid \<Rightarrow> unit kernel"

consts'
loadHWASID :: "asid \<Rightarrow> (hardware_asid option) kernel"

consts'
invalidateASID :: "asid \<Rightarrow> unit kernel"

consts'
invalidateHWASIDEntry :: "hardware_asid \<Rightarrow> unit kernel"

consts'
invalidateASIDEntry :: "asid \<Rightarrow> unit kernel"

consts'
findFreeHWASID :: "hardware_asid kernel"

consts'
getHWASID :: "asid \<Rightarrow> hardware_asid kernel"

consts'
doFlush :: "flush_type \<Rightarrow> vptr \<Rightarrow> vptr \<Rightarrow> paddr \<Rightarrow> unit machine_monad"

consts'
flushPage :: "vmpage_size \<Rightarrow> machine_word \<Rightarrow> asid \<Rightarrow> vptr \<Rightarrow> unit kernel"

consts'
flushTable :: "machine_word \<Rightarrow> asid \<Rightarrow> vptr \<Rightarrow> unit kernel"

consts'
flushSpace :: "asid \<Rightarrow> unit kernel"

consts'
invalidateTLBByASID :: "asid \<Rightarrow> unit kernel"

consts'
labelToFlushType :: "machine_word \<Rightarrow> flush_type"

consts'
pageBase :: "vptr \<Rightarrow> vmpage_size \<Rightarrow> vptr"

consts'
resolveVAddr :: "machine_word \<Rightarrow> vptr \<Rightarrow> ((vmpage_size * paddr) option) kernel"

consts'
decodeARMMMUInvocation :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> cptr \<Rightarrow> machine_word \<Rightarrow> arch_capability \<Rightarrow> (capability * machine_word) list \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
decodeARMPageFlush :: "machine_word \<Rightarrow> machine_word list \<Rightarrow> arch_capability \<Rightarrow> ( syscall_error , invocation ) kernel_f"

consts'
checkVPAlignment :: "vmpage_size \<Rightarrow> vptr \<Rightarrow> ( syscall_error , unit ) kernel_f"

consts'
checkValidMappingSize :: "vmpage_size \<Rightarrow> unit kernel"

consts'
performARMMMUInvocation :: "invocation \<Rightarrow> machine_word list kernel_p"

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
storePDE :: "machine_word \<Rightarrow> pde \<Rightarrow> unit kernel"

consts'
storePTE :: "machine_word \<Rightarrow> pte \<Rightarrow> unit kernel"


end
end
