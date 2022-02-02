--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the encoding of arch-specific faults.

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.

module SEL4.API.Failures.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine

-- note that typically the first word of vmFaultArchData corresponds to
-- "instructionFault", while the second to "FSR", in opposite order to C, where
-- "instructionFault" is the second, boolean, argument

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
