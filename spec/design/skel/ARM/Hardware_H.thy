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
  "../../machine/ARM/MachineOps"
  State_H
begin
context Arch begin global_naming ARM_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs Platform=Platform.ARM CONTEXT ARM_H NOT getMemoryRegions getDeviceRegions getKernelDevices loadWord storeWord storeWordVM getActiveIRQ ackInterrupt maskInterrupt configureTimer resetTimer debugPrint getRestartPC setNextPC clearMemory clearMemoryVM initMemory freeMemory writeTTBR0 setCurrentPD setGlobalPD  setTTBCR setHardwareASID invalidateTLB invalidateTLB_ASID invalidateTLB_VAASID cleanByVA cleanByVA_PoU invalidateByVA invalidateByVA_I invalidate_I_PoU cleanInvalByVA branchFlush clean_D_PoU cleanInvalidate_D_PoC cleanInvalidate_D_PoU cleanInvalidateL2Range invalidateL2Range cleanL2Range isb dsb dmb getIFSR getDFSR getFAR HardwareASID wordFromPDE wordFromPTE VMFaultType VMPageSize pageBits pageBitsForSize toPAddr cacheLineBits cacheLine lineStart cacheRangeOp cleanCacheRange_PoC cleanInvalidateCacheRange_RAM cleanCacheRange_RAM cleanCacheRange_PoU invalidateCacheRange_RAM invalidateCacheRange_I branchFlushRange cleanCaches_PoU cleanInvalidateL1Caches addrFromPPtr ptrFromPAddr initIRQController MachineData

end

context begin interpretation Arch .
requalify_types vmrights
end

context Arch begin global_naming ARM_H

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM_H instanceproofs NOT HardwareASID VMFaultType VMPageSize

#INCLUDE_HASKELL SEL4/Machine/Hardware/ARM.lhs CONTEXT ARM_H ONLY wordFromPDE wordFromPTE

end
end
