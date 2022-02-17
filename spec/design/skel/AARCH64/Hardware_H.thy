(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory Hardware_H
imports
  MachineOps
  State_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs Platform=Platform.AARCH64 CONTEXT AARCH64_H NOT plic_complete_claim getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory setHardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr addrFromPPtr ptrFromPAddr sfence physBase paddrBase pptrBase pptrBaseOffset pptrUserTop kernelELFBase kernelELFBaseOffset kernelELFPAddrBase addrFromKPPtr ptTranslationBits vmFaultTypeFSR read_stval setVSpaceRoot hwASIDFlush setIRQTrigger

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs CONTEXT AARCH64_H instanceproofs NOT plic_complete_claim HardwareASID VMFaultType VMPageSize VMPageEntry HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/AARCH64.hs CONTEXT AARCH64_H ONLY wordFromPTE

end (* context AARCH64 *)

end
