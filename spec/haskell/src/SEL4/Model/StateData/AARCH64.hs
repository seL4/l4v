--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains the architecture-specific kernel global data for the
-- RISCV 64bit architecture.

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.

module SEL4.Model.StateData.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Machine.Hardware.AARCH64 (PTE(..))
import SEL4.Object.Structures.AARCH64

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
