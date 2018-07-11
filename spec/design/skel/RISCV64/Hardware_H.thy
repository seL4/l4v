(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory Hardware_H
imports
  "../../machine/RISCV64/MachineOps"
  State_H
begin

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs Platform=Platform.RISCV64 CONTEXT RISCV64_H NOT getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory setHardwareASID wordFromPDE wordFromPTE VMFaultType HypFaultType VMPageSize pageBits pageBitsForSize toPAddr addrFromPPtr ptrFromPAddr sfence physBase ptTranslationBits vmFaultTypeFSR read_sbadaddr setVMRoot hwASIDFlush

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64_H instanceproofs NOT HardwareASID VMFaultType VMPageSize VMPageEntry HypFaultType

#INCLUDE_HASKELL SEL4/Machine/Hardware/RISCV64.hs CONTEXT RISCV64_H ONLY wordFromPTE

end (* context RISCV64 *)

end
