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

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM_HYP.lhs Platform=Platform.ARM_HYP CONTEXT ARM_HYP_H NOT getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory writeTTBR0 setCurrentPD setGlobalPD  setTTBCR setHardwareASID invalidateTLB invalidateTLB_ASID invalidateTLB_VAASID cleanByVA cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidate_D_PoU cleanInvalidateL2Range invalidateL2Range cleanL2Range isb dsb dmb getIFSR getDFSR getFAR HardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr cacheLineBits cacheLine lineStart cacheRangeOp cleanCacheRange_PoC cleanInvalidateCacheRange_RAM cleanCacheRange_RAM cleanCacheRange_PoU invalidateCacheRange_RAM invalidateCacheRange_I branchFlushRange cleanCaches_PoU cleanInvalidateL1Caches addrFromPPtr ptrFromPAddr initIRQController MachineData hapFromVMRights wordsFromPDE wordsFromPTE writeContextIDAndPD hcrVCPU hcrNative vgicHCREN sctlrDefault actlrDefault gicVCPUMaxNumLR getHSR setHCR getHDFAR addressTranslateS1CPR getSCTLR setSCTLR getACTLR setACTLR get_gic_vcpu_ctrl_hcr set_gic_vcpu_ctrl_hcr get_gic_vcpu_ctrl_vmcr set_gic_vcpu_ctrl_vmcr get_gic_vcpu_ctrl_apr set_gic_vcpu_ctrl_apr get_gic_vcpu_ctrl_vtr get_gic_vcpu_ctrl_eisr0 get_gic_vcpu_ctrl_eisr1 get_gic_vcpu_ctrl_misr get_gic_vcpu_ctrl_lr set_gic_vcpu_ctrl_lr setCurrentPDPL2 set_lr_svc set_sp_svc set_lr_abt set_sp_abt set_lr_und set_sp_und set_lr_irq set_sp_irq set_lr_fiq set_sp_fiq set_r8_fiq set_r9_fiq set_r10_fiq set_r11_fiq set_r12_fiq get_lr_svc get_sp_svc get_lr_abt get_sp_abt get_lr_und get_sp_und get_lr_irq get_sp_irq get_lr_fiq get_sp_fiq get_r8_fiq get_r9_fiq get_r10_fiq get_r11_fiq get_r12_fiq

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM_HYP.lhs CONTEXT ARM_HYP_H instanceproofs NOT HardwareASID VMFaultType HypFaultType VMPageSize

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM_HYP.lhs CONTEXT ARM_HYP_H ONLY hapFromVMRights wordsFromPDE wordsFromPTE

end
end
