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

context Arch begin arch_global_naming (H)

definition ticksToUs :: "word64 \<Rightarrow> word64" where
  "ticksToUs \<equiv> ticks_to_us"

definition maxUsToTicks :: "word64" where
  "maxUsToTicks \<equiv> max_us_to_ticks"

definition maxTicksToUs :: "word64" where
  "maxTicksToUs \<equiv> max_ticks_to_us"

definition kernelWCETTicks :: "word64" where
  "kernelWCETTicks \<equiv> kernelWCET_ticks"

definition kernelWCETUs :: "word64" where
  "kernelWCETUs \<equiv> kernelWCET_us"

definition maxPeriodUs :: "word64" where
  "maxPeriodUs \<equiv> MAX_PERIOD_US"

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs Platform=Platform.ARM CONTEXT ARM_H NOT getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt deactivateInterrupt setDeadline configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory writeTTBR0 setGlobalPD  setTTBCR setHardwareASID invalidateLocalTLB invalidateLocalTLB_ASID invalidateLocalTLB_VAASID cleanByVA cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidate_D_PoU cleanInvalidateL2Range invalidateL2Range cleanL2Range isb dsb dmb getIFSR getDFSR getFAR HardwareASID wordFromPDE wordFromPTE VMFaultType VMPageSize HypFaultType pageBits pageBitsForSize toPAddr cacheLineBits cacheLine lineStart cacheRangeOp cleanCacheRange_PoC cleanInvalidateCacheRange_RAM cleanCacheRange_RAM cleanCacheRange_PoU invalidateCacheRange_RAM invalidateCacheRange_I branchFlushRange cleanCaches_PoU cleanInvalidateL1Caches addrFromPPtr ptrFromPAddr initIRQController setIRQTrigger MachineData paddrBase pptrBase pptrTop paddrTop kernelELFPAddrBase kernelELFBase kernelELFBaseOffset pptrBaseOffset addrFromKPPtr config_ARM_GIC_V3 sendSGI numSGIs gicNumTargets isGICPlatform haveSetTrigger handleSpuriousIRQ_mop hasSpuriousIRQ_mop getCurrentTime usToTicks ticksToUs maxUsToTicks maxTicksToUs maxPeriodUs ackDeadlineIRQ timerPrecision

end

arch_requalify_types (H)
  vmrights

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM_H instanceproofs NOT HardwareASID VMFaultType VMPageSize HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM_H ONLY wordFromPDE wordFromPTE

(* Kernel_Config provides a generic numeral, Haskell expects type irq *)
abbreviation (input) maxIRQ :: irq where
  "maxIRQ == Kernel_Config.maxIRQ"

(* provide ARM/ARM_HYP machine op in _H global_prefix for arch-split *)
abbreviation (input) initIRQController where
  "initIRQController \<equiv> ARM.initIRQController"

end
end
