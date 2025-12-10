--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

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
import SEL4.API.Invocation
import SEL4.API.Invocation.RISCV64 as ArchInv
import SEL4.API.InvocationLabels.RISCV64 as ArchLabels
import {-# SOURCE #-} SEL4.Object.CNode
import {-# SOURCE #-} SEL4.Kernel.CSpace
import {-# SOURCE #-} SEL4.Object.Interrupt
import qualified SEL4.Machine.Hardware.RISCV64 as Arch
import SEL4.Machine.Hardware.RISCV64.PLATFORM (irqInvalid)

decodeIRQControlInvocation :: Word -> [Word] -> PPtr CTE -> [Capability] ->
        KernelF SyscallError ArchInv.IRQControlInvocation
decodeIRQControlInvocation label args srcSlot extraCaps =
    case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel ArchLabels.RISCVIRQIssueIRQHandler,
            irqW:triggerW:index:depth:_, cnode:_) -> do
            checkIRQ irqW
            let irq = toEnum (fromIntegral irqW) :: IRQ
            irqActive <- withoutFailure $ isIRQActive irq
            when irqActive $ throw RevokeFirst
            destSlot <- lookupTargetSlot cnode
                (CPtr index) (fromIntegral depth)
            ensureEmptySlot destSlot
            return $
                ArchInv.IssueIRQHandler irq destSlot srcSlot (triggerW /= 0)
        (ArchInvocationLabel ArchLabels.RISCVIRQIssueIRQHandler,_,_) ->
            throw TruncatedMessage
        _ -> throw IllegalOperation

performIRQControl :: ArchInv.IRQControlInvocation -> KernelP ()
performIRQControl (ArchInv.IssueIRQHandler (IRQ irq) destSlot srcSlot trigger)
    = withoutPreemption $ do
    doMachineOp $ Arch.setIRQTrigger irq trigger
    -- do same thing as generic path in performIRQControl in Interrupt.lhs
    setIRQState IRQSignal (IRQ irq)
    cteInsert (IRQHandlerCap (IRQ irq)) srcSlot destSlot
    return ()

plic_complete_claim :: IRQ -> MachineMonad ()
plic_complete_claim (IRQ irq) = Arch.plic_complete_claim irq

invokeIRQHandler :: IRQHandlerInvocation -> Kernel ()
invokeIRQHandler (AckIRQ irq) = doMachineOp $ plic_complete_claim irq
invokeIRQHandler _ = return ()

handleSpuriousIRQ :: Kernel ()
handleSpuriousIRQ = return ()

handleReservedIRQ :: IRQ -> Kernel ()
handleReservedIRQ _ = return ()

maskIrqSignal :: IRQ -> Kernel ()
maskIrqSignal _ = return ()

initInterruptController :: Kernel ()
initInterruptController = error "Unimplemented. Init code."

checkIRQ :: Word -> KernelF SyscallError ()
checkIRQ irqW = when (irqW > fromIntegral (fromEnum maxIRQ) ||
                      irqW == fromIntegral (fromEnum irqInvalid)) $
    throw $ RangeError 1 (fromIntegral (fromEnum maxIRQ))
