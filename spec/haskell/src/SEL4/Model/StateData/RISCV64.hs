-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module contains the architecture-specific kernel global data for the
-- RISCV 64bit architecture.

module SEL4.Model.StateData.RISCV64 where

import SEL4.Machine
import SEL4.Machine.Hardware.RISCV64 (PTE(..))
import SEL4.Object.Structures.RISCV64

import Data.Array

-- used in proofs only
data RISCVVSpaceRegionUse
    = RISCVVSpaceUserRegion
    | RISCVVSpaceInvalidRegion
    | RISCVVSpaceKernelWindow
    | RISCVVSpaceKernelELFWindow
    | RISCVVSpaceDeviceWindow

data KernelState = RISCVKernelState {
    riscvKSASIDTable :: Array ASID (Maybe (PPtr ASIDPool)),
    riscvKSGlobalPT :: PPtr PTE }

newKernelState :: PAddr -> (KernelState, [PAddr])
newKernelState _ = error "No initial state defined for RISC-V"
