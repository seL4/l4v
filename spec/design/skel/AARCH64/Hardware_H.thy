(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Hardware_H
imports
  MachineOps
  State_H
begin

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs Platform=Platform.AARCH64 CONTEXT AARCH64_H \
  NOT PT_Type plic_complete_claim getMemoryRegions getDeviceRegions getKernelDevices \
  loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt \
  configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory \
  clearMemoryVM initMemory freeMemory setHardwareASID wordFromPDE wordFromPTE \
  VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr \
  addrFromPPtr ptrFromPAddr sfence physBase paddrBase pptrBase pptrBaseOffset \
  pptrUserTop kernelELFBase kernelELFBaseOffset kernelELFPAddrBase \
  addrFromKPPtr ptTranslationBits vmFaultTypeFSR setVSpaceRoot \
  setIRQTrigger \
  config_ARM_PA_SIZE_BITS_40 fpuThreadDeleteOp isFpuEnable \
  hcrVCPU hcrNative sctlrDefault vgicHCREN gicVCPUMaxNumLR sctlrEL1VM \
  get_gic_vcpu_ctrl_hcr set_gic_vcpu_ctrl_hcr get_gic_vcpu_ctrl_vmcr \
  set_gic_vcpu_ctrl_vmcr get_gic_vcpu_ctrl_apr set_gic_vcpu_ctrl_apr \
  get_gic_vcpu_ctrl_vtr get_gic_vcpu_ctrl_eisr0 get_gic_vcpu_ctrl_eisr1 \
  get_gic_vcpu_ctrl_misr get_gic_vcpu_ctrl_lr set_gic_vcpu_ctrl_lr read_cntpct \
  check_export_arch_timer \
  isb dsb dmb \
  invalidateTranslationASID invalidateTranslationSingle \
  cleanByVA_PoU cleanInvalidateCacheRange_RAM cleanCacheRange_RAM cleanCacheRange_PoU \
  invalidateCacheRange_RAM invalidateCacheRange_I branchFlushRange \
  enableFpuEL01 \
  getFAR getDFSR getIFSR getHSR setHCR getESR  getSCTLR setSCTLR \
  addressTranslateS1 \
  readVCPUHardwareReg writeVCPUHardwareReg vcpuBits

end

arch_requalify_types (H)
  vmrights

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs CONTEXT AARCH64_H instanceproofs NOT plic_complete_claim HardwareASID VMFaultType VMPageSize VMPageEntry HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs CONTEXT AARCH64_H ONLY wordFromPTE

(* Kernel_Config provides a generic numeral, Haskell expects type irq *)
abbreviation (input) maxIRQ :: irq where
  "maxIRQ \<equiv> Kernel_Config.maxIRQ"

end (* context AARCH64 *)

end
