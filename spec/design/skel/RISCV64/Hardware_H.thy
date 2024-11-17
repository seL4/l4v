(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Hardware_H
imports
  MachineOps
  State_H
begin

context Arch begin arch_global_naming (H)

definition usToTicks :: "word64 \<Rightarrow> word64" where
  "usToTicks \<equiv> us_to_ticks"

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

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs Platform=Platform.RISCV64 CONTEXT RISCV64_H NOT plic_complete_claim getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt setDeadline configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory setHardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr addrFromPPtr ptrFromPAddr ptTranslationBits vmFaultTypeFSR read_sbadaddr setVSpaceRoot hwASIDFlush setIRQTrigger addrFromPPtr ptrFromPAddr sfence physBase paddrBase pptrBase pptrBaseOffset pptrTop pptrUserTop kernelELFBase kernelELFBaseOffset kernelELFPAddrBase addrFromKPPtr ptTranslationBits vmFaultTypeFSR read_stval setVSpaceRoot hwASIDFlush setIRQTrigger getCurrentTime usToTicks ticksToUs maxUsToTicks maxTicksToUs maxPeriodUs ackDeadlineIRQ

end

arch_requalify_types (H)
  vmrights

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64_H instanceproofs NOT plic_complete_claim HardwareASID VMFaultType VMPageSize VMPageEntry HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64_H ONLY wordFromPTE

(* Unlike on Arm architectures, maxIRQ comes from Platform definitions.
   We provide this abbreviation to match arch-split expectations. *)
abbreviation (input) maxIRQ :: irq where
  "maxIRQ \<equiv> Platform.RISCV64.maxIRQ"

end (* context RISCV64 *)

end
