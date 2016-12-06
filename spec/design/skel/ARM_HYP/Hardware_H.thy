(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Hardware_H
imports
  "../../machine/ARM_HYP/MachineOps"
  State_H
begin
context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM_HYP.lhs Platform=Platform.ARM_HYP CONTEXT ARM_HYP_H NOT getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory writeTTBR0 setCurrentPD setGlobalPD  setTTBCR setHardwareASID invalidateTLB invalidateTLB_ASID invalidateTLB_VAASID cleanByVA cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidate_D_PoU cleanInvalidateL2Range invalidateL2Range cleanL2Range isb dsb dmb getIFSR getDFSR getFAR HardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr cacheLineBits cacheLine lineStart cacheRangeOp cleanCacheRange_PoC cleanInvalidateCacheRange_RAM cleanCacheRange_RAM cleanCacheRange_PoU invalidateCacheRange_RAM invalidateCacheRange_I branchFlushRange cleanCaches_PoU cleanInvalidateL1Caches addrFromPPtr ptrFromPAddr initIRQController MachineData hapFromVMRights wordsFromPDE wordsFromPTE writeContextIDAndPD getHSR setHCR getHDFAR addressTranslateS1CPR getSCTLR setSCTLR getACTLR setACTLR get_gic_vcpu_ctrl_hcr set_gic_vcpu_ctrl_hcr get_gic_vcpu_ctrl_vmcr set_gic_vcpu_ctrl_vmcr get_gic_vcpu_ctrl_apr set_gic_vcpu_ctrl_apr get_gic_vcpu_ctrl_vtr get_gic_vcpu_ctrl_eisr0 get_gic_vcpu_ctrl_eisr1 get_gic_vcpu_ctrl_misr get_gic_vcpu_ctrl_lr set_gic_vcpu_ctrl_lr

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM_HYP.lhs CONTEXT ARM_HYP_H instanceproofs NOT HardwareASID VMFaultType HypFaultType VMPageSize

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM_HYP.lhs CONTEXT ARM_HYP_H ONLY hapFromVMRights wordsFromPDE wordsFromPTE

end
end
