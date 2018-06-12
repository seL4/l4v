-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module defines the handling of the RISC-V hardware-defined page tables.

module SEL4.Kernel.VSpace.RISCV64 where

import SEL4.API.Types
import SEL4.API.Failures
import SEL4.API.Failures.RISCV64
import SEL4.Machine.RegisterSet
import SEL4.Machine.RegisterSet.RISCV64 (Register(..))
import SEL4.Machine.Hardware.RISCV64
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Model.StateData.RISCV64
import SEL4.API.InvocationLabels
import SEL4.API.InvocationLabels.RISCV64
import {-# SOURCE #-} SEL4.Object.CNode
import {-# SOURCE #-} SEL4.Object.TCB
import {-# SOURCE #-} SEL4.Kernel.Init
import {-# SOURCE #-} SEL4.Kernel.CSpace

import Data.Bits
import Data.Maybe
import Data.Array
import Data.Word (Word32)

-- The RISC-V-specific invocations are imported with the "ArchInv" prefix. This
-- is necessary to avoid namespace conflicts with the generic invocations.

import SEL4.API.Invocation.RISCV64 as ArchInv

{- Constants -}

-- FIXME RISCV TODO

{- Creating a New Address Space -}

-- FIXME RISCV TODO

{- Lookups and Faults -}

{- IPC Buffer Accesses -}

lookupIPCBuffer :: Bool -> PPtr TCB -> Kernel (Maybe (PPtr Word))
lookupIPCBuffer isReceiver thread = error "FIXME RISCV TODO"

-- FIXME RISCV TODO

{- ASID Lookups -}

-- FIXME RISCV TODO

{- Locating Page Table and Page Directory Slots -}

-- FIXME RISCV TODO

{- Handling Faults -}

handleVMFault :: PPtr TCB -> VMFaultType -> KernelF Fault ()
handleVMFault thread f = error "FIXME RISCV TODO"

-- FIXME RISCV TODO

{- Unmapping and Deletion -}

-- When a capability backing a virtual memory mapping is deleted, or when an
-- explicit request is made to remove a mapping, the kernel must locate the
-- corresponding entries in the page table or ASID table and remove them. It is
-- also necessary to flush the removed mappings from the hardware caches.

{- Deleting an ASID Pool -}

-- FIXME RISCV TODO

{- Deleting an Address Space -}

-- FIXME RISCV TODO

{- Deleting a Page Table -}

-- FIXME RISCV TODO

{- Unmapping a Frame -}

-- FIXME RISCV TODO

{- Address Space Switching -}

-- FIXME RISCV TODO

setVMRoot :: PPtr TCB -> Kernel ()
setVMRoot tcb = error "FIXME RISCV TODO"

{- Helper Functions -}

checkValidIPCBuffer :: VPtr -> Capability -> KernelF SyscallError ()
checkValidIPCBuffer = error "FIXME RISCV TODO"

isValidVTableRoot :: Capability -> Bool
isValidVTableRoot = error "FIXME RISCV TODO"

-- FIXME RISCV TODO

{- Flushing -}

-- FIXME RISCV TODO

{- Managing ASID Map -}

-- FIXME RISCV TODO

{- Decoding RISC-V Invocations -}

-- FIXME RISCV TODO

decodeRISCVMMUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation

decodeRISCVMMUInvocation _ _ _ _ _ _ = fail "Unreachable"  -- FIXME RISCV TODO

{- Invocation Implementations -}

-- FIXME RISCV TODO

{- Boot Code and Unimplemented Stubs -}

-- FIXME RISCV unchecked copypasta for this whole part

mapKernelWindow  :: Kernel ()
mapKernelWindow = error "boot code unimplemented"

activateGlobalVSpace :: Kernel ()
activateGlobalVSpace = error "boot code unimplemented"

createIPCBufferFrame :: Capability -> VPtr -> KernelInit Capability
createIPCBufferFrame = error "boot code unimplemented"

createBIFrame :: Capability -> VPtr -> Word32 -> Word32 -> KernelInit Capability
createBIFrame = error "boot code unimplemented"

createFramesOfRegion :: Capability -> Region -> Bool -> KernelInit ()
createFramesOfRegion = error "boot code unimplemented"

createITPDPTs :: Capability -> VPtr -> VPtr -> KernelInit Capability
createITPDPTs  = error "boot code unimplemented"

writeITPDPTs :: Capability -> Capability -> KernelInit ()
writeITPDPTs  = error "boot code unimplemented"

createITASIDPool :: Capability -> KernelInit Capability
createITASIDPool  = error "boot code unimplemented"

writeITASIDPool :: Capability -> Capability -> Kernel ()
writeITASIDPool  = error "boot code unimplemented"

createDeviceFrames :: Capability -> KernelInit ()
createDeviceFrames  = error "boot code unimplemented"

vptrFromPPtr :: PPtr a -> KernelInit VPtr
vptrFromPPtr  = error "boot code unimplemented"
