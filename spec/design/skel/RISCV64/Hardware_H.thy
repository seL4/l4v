(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Hardware_H
imports
  "../../machine/RISCV64/MachineOps"
  State_H
begin

context Arch begin global_naming RISCV64_H

definition usToTicks :: "word64 \<Rightarrow> word64" where
  "usToTicks \<equiv> us_to_ticks"

definition ticksToUs :: "word64 \<Rightarrow> word64" where
  "ticksToUs \<equiv> ticks_to_us"

definition maxUsToTicks :: "word64" where
  "maxUsToTicks \<equiv> 60 * 60 * 1000" (* FIXME RT: sync with aspec and C *)

definition maxTicksToUs :: "word64" where
  "maxTicksToUs \<equiv> max_ticks_to_us"

definition kernelWCETTicks :: "word64" where
  "kernelWCETTicks \<equiv> kernelWCET_ticks"

definition kernelWCETUs :: "word64" where
  "kernelWCETUs \<equiv> kernelWCET_us"

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs Platform=Platform.RISCV64 CONTEXT RISCV64_H NOT plic_complete_claim getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt setDeadline configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory setHardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr addrFromPPtr ptrFromPAddr sfence physBase ptTranslationBits vmFaultTypeFSR read_sbadaddr setVSpaceRoot hwASIDFlush setIRQTrigger getCurrentTime usToTicks ticksToUs maxUsToTicks maxTicksToUs ackDeadlineIRQ

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64_H instanceproofs NOT plic_complete_claim HardwareASID VMFaultType VMPageSize VMPageEntry HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64_H ONLY wordFromPTE

end (* context RISCV64 *)

end
