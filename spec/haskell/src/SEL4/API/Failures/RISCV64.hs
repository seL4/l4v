-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

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
