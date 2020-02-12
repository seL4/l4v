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

import Prelude hiding (Word)
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
    riscvKSGlobalPTs :: Int -> [PPtr PTE],
    riscvKSKernelVSpace :: PPtr Word -> RISCVVSpaceRegionUse
  }

-- counting from 0 at bottom, i.e. number of levels = maxPTLevel + 1;
-- maxPTLevel = level of top-level root table
maxPTLevel :: Int
maxPTLevel = 2

riscvKSGlobalPT :: KernelState -> PPtr PTE
riscvKSGlobalPT s = head (riscvKSGlobalPTs s maxPTLevel)

newKernelState :: PAddr -> (KernelState, [PAddr])
newKernelState _ = error "No initial state defined for RISC-V"
