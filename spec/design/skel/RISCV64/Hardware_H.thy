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

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs Platform=Platform.RISCV64 CONTEXT RISCV64_H NOT plic_complete_claim getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory setHardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr addrFromPPtr ptrFromPAddr sfence physBase paddrBase pptrBase pptrBaseOffset pptrTop pptrUserTop kernelELFBase kernelELFBaseOffset kernelELFPAddrBase addrFromKPPtr ptTranslationBits vmFaultTypeFSR read_stval setVSpaceRoot hwASIDFlush setIRQTrigger

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64_H instanceproofs NOT plic_complete_claim HardwareASID VMFaultType VMPageSize VMPageEntry HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64_H ONLY wordFromPTE

end (* context RISCV64 *)

end
