(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Hardware_H
imports
  MachineOps
  State_H
begin
context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs Platform=Platform.ARM_HYP CONTEXT ARM_HYP_H NOT getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory writeTTBR0 setGlobalPD  setTTBCR setHardwareASID invalidateLocalTLB invalidateLocalTLB_ASID invalidateLocalTLB_VAASID cleanByVA cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidate_D_PoU cleanInvalidateL2Range invalidateL2Range cleanL2Range isb dsb dmb getIFSR getDFSR getFAR HardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr paddrBase pptrBase pptrTop paddrTop kernelELFPAddrBase kernelELFBase kernelELFBaseOffset pptrBaseOffset cacheLineBits cacheLine lineStart cacheRangeOp cleanCacheRange_PoC cleanInvalidateCacheRange_RAM cleanCacheRange_RAM cleanCacheRange_PoU invalidateCacheRange_RAM invalidateCacheRange_I branchFlushRange cleanCaches_PoU cleanInvalidateL1Caches addrFromPPtr ptrFromPAddr addrFromKPPtr initIRQController MachineData hapFromVMRights wordsFromPDE wordsFromPTE writeContextIDAndPD hcrVCPU hcrNative vgicHCREN sctlrDefault actlrDefault gicVCPUMaxNumLR getHSR setHCR getHDFAR addressTranslateS1 getSCTLR setSCTLR getACTLR setACTLR get_gic_vcpu_ctrl_hcr set_gic_vcpu_ctrl_hcr get_gic_vcpu_ctrl_vmcr set_gic_vcpu_ctrl_vmcr get_gic_vcpu_ctrl_apr set_gic_vcpu_ctrl_apr get_gic_vcpu_ctrl_vtr get_gic_vcpu_ctrl_eisr0 get_gic_vcpu_ctrl_eisr1 get_gic_vcpu_ctrl_misr get_gic_vcpu_ctrl_lr set_gic_vcpu_ctrl_lr setCurrentPDPL2 readVCPUHardwareReg setIRQTrigger writeVCPUHardwareReg getTPIDRURO setTPIDRURO get_cntv_cval_64 set_cntv_cval_64 set_cntv_off_64 get_cntv_off_64 read_cntpct

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM_HYP_H instanceproofs NOT HardwareASID VMFaultType HypFaultType VMPageSize

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM_HYP_H ONLY hapFromVMRights wordsFromPDE wordsFromPTE

(* Kernel_Config provides a generic numeral, Haskell expects type irq *)
abbreviation (input) maxIRQ :: irq where
  "maxIRQ == Kernel_Config.maxIRQ"

end
end
