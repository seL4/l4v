-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module defines the machine-specific interrupt handling routines.

{-# LANGUAGE CPP #-}

module SEL4.Object.Interrupt.RISCV64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Model
import SEL4.Object.Structures
import SEL4.API.Failures
import SEL4.API.Types
import SEL4.API.InvocationLabels
import SEL4.API.Invocation.RISCV64 as ArchInv
import SEL4.API.InvocationLabels.RISCV64 as ArchLabels
import {-# SOURCE #-} SEL4.Object.CNode
import {-# SOURCE #-} SEL4.Kernel.CSpace
import {-# SOURCE #-} SEL4.Object.Interrupt
import qualified SEL4.Machine.Hardware.RISCV64 as Arch

-- at this time, interrupts don't really exist on the target platform
decodeIRQControlInvocation :: Word -> [Word] -> PPtr CTE -> [Capability] ->
        KernelF SyscallError ArchInv.IRQControlInvocation
decodeIRQControlInvocation label args srcSlot extraCaps =
    throw IllegalOperation

performIRQControl :: ArchInv.IRQControlInvocation -> KernelP ()
performIRQControl = error "Unreachable due to no IRQControl decode on this arch."

handleReservedIRQ :: IRQ -> Kernel ()
handleReservedIRQ _ = return ()

initInterruptController :: Kernel ()
initInterruptController = error "Unimplemented. Init code."

checkIRQ :: Word -> KernelF SyscallError ()
checkIRQ irq = throw IllegalOperation
