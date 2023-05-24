--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains the architecture-specific kernel global data for the
-- AAarch64 architecture.

module SEL4.Model.StateData.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Machine.Hardware.AARCH64 (PTE(..), PT_Type, config_ARM_PA_SIZE_BITS_40)
import SEL4.Object.Structures.AARCH64

import Data.Array

-- ArmVSpaceKernelELFWindow currently still unused in those kernel mappings, but
-- planned for kernel image clone and mapping kernel ELF with different
-- permissions.
data ArmVSpaceRegionUse
    = ArmVSpaceUserRegion
    | ArmVSpaceInvalidRegion
    | ArmVSpaceKernelWindow
    | ArmVSpaceDeviceWindow


data KernelState = ARMKernelState {
    -- mapping ASID high bits to ASID pools:
    armKSASIDTable :: Array ASID (Maybe (PPtr ASIDPool)),
    -- used in proofs only, to model effect of kernel mappings abstractly:
    armKSKernelVSpace :: PPtr Word -> ArmVSpaceRegionUse,
    -- map VM IDs to seL4 ASIDs; the space of VM IDs is smaller than the ASID
    -- space, so the kernel allocates and displaces on demand.
    armKSVMIDTable :: Array VMID (Maybe ASID),
    armKSNextVMID :: VMID,
    -- pointer to a global top-level VSpace table with only invalid entries;
    -- used e.g. for user threads with missing or invalid VSpace root
    armKSGlobalUserVSpace :: PPtr PTE,
    armHSCurVCPU :: Maybe (PPtr VCPU, Bool),
    armKSGICVCPUNumListRegs :: Int,
    gsPTTypes :: Word -> Maybe PT_Type
    }

-- counting from 0 at bottom, i.e. number of levels = maxPTLevel + 1;
-- maxPTLevel = level of top-level root table
maxPTLevel :: Int
maxPTLevel = if config_ARM_PA_SIZE_BITS_40 then 2 else 3

newKernelState :: PAddr -> (KernelState, [PAddr])
newKernelState _ = error "No initial state defined for AARCH64"
