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

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs Platform=Platform.X64 CONTEXT X64_H NOT getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory wordFromPDE wordFromPTE VMFaultType HypFaultType VMMapType VMPageSize pageBits pageBitsForSize paddrBase pptrBase pptrTop pptrBaseOffset kernelELFBaseOffset kernelELFPAddrBase kernelELFBase toPAddr addrFromPPtr ptrFromPAddr addrFromKPPtr setCurrentUserCR3 getCurrentUserCR3 invalidateTLB invalidateTLBEntry mfence wordFromPML4E wordFromPDPTE firstValidIODomain numIODomainIDBits hwASIDInvalidate getFaultAddress irqIntOffset maxPCIBus maxPCIDev maxPCIFunc ioapicIRQLines ioapicMapPinToVector irqStateIRQIOAPICNew irqStateIRQMSINew updateIRQState in8 out8 in16 out16 in32 out32 invalidatePageStructureCache writeCR3 invalidateASID invalidateTranslationSingleASID invalidateLocalPageStructureCacheASID ptTranslationBits nativeThreadUsingFPU switchFpuOwner

end

arch_requalify_types (H)
  vmrights

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs CONTEXT X64_H instanceproofs NOT VMFaultType VMPageSize VMPageEntry VMMapType HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/X64.lhs CONTEXT X64_H ONLY wordFromPDE wordFromPTE wordFromPML4E wordFromPDPTE

(* Unlike on Arm architectures, maxIRQ comes from Platform definitions.
   We provide this abbreviation to match arch-split expectations. *)
abbreviation (input) maxIRQ :: irq where
  "maxIRQ \<equiv> Platform.X64.maxIRQ"

end (* context X64 *)

end
