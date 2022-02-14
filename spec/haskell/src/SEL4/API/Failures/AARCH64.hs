--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
-- Copyright 2022, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the encoding of arch-specific faults.

module SEL4.API.Failures.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine

-- note that typically the first word of vmFaultArchData corresponds to
-- "instructionFault", while the second to "FSR", in opposite order to C, where
-- "instructionFault" is the second, boolean, argument
-- Note: AArch64 HSR/FSR are still stored as 32-bit in C

data ArchFault
    = VMFault {
            vmFaultAddress :: VPtr,
            vmFaultArchData :: [Word] }
    | VCPUFault {
            vcpuHSR :: Word }
    | VPPIEvent {
            vppiIRQ :: IRQ }
    | VGICMaintenance { vgicMaintenanceData :: Maybe Word }
    deriving Show
