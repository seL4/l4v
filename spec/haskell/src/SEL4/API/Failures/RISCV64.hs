--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the encoding of arch-specific faults.

module SEL4.API.Failures.RISCV64 where

import Prelude hiding (Word)
import SEL4.Machine

-- note that typically the first word of vmFaultArchData corresponds to
-- "instructionFault", while the second to "FSR", in opposite order to C, where
-- "instructionFault" is the second, boolean, argument

data ArchFault
    = VMFault {
            vmFaultAddress :: VPtr,
            vmFaultArchData :: [Word] }
    deriving Show
