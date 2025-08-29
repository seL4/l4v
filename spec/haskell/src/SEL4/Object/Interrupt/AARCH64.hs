--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the machine-specific interrupt handling routines.

{-# LANGUAGE CPP #-}

module SEL4.Object.Interrupt.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Model
import SEL4.Object.Structures
import SEL4.API.Failures
import SEL4.API.Types
import SEL4.API.InvocationLabels
import SEL4.API.Invocation
import SEL4.API.Invocation.AARCH64 as ArchInv
import SEL4.API.InvocationLabels.AARCH64 as ArchLabels
import {-# SOURCE #-} SEL4.Object.CNode
import {-# SOURCE #-} SEL4.Kernel.CSpace
import {-# SOURCE #-} SEL4.Object.Interrupt
import SEL4.Machine.Hardware.AARCH64 (config_ARM_GIC_V3, deactivateInterrupt)
import qualified SEL4.Machine.Hardware.AARCH64 as Arch
import SEL4.Machine.Hardware.AARCH64.PLATFORM (irqInvalid)
import SEL4.Object.VCPU.TARGET (vgicMaintenance, vppiEvent, irqVPPIEventIndex)
import SEL4.Machine.Hardware.AARCH64.PLATFORM (irqVGICMaintenance, irqVTimerEvent, irqSMMU)

decodeIRQControlInvocation :: Word -> [Word] -> PPtr CTE -> [Capability] ->
        KernelF SyscallError ArchInv.IRQControlInvocation
decodeIRQControlInvocation label args srcSlot extraCaps =
    case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel ArchLabels.ARMIRQIssueIRQHandlerTrigger,
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
        (ArchInvocationLabel ArchLabels.ARMIRQIssueIRQHandlerTrigger,_,_) ->
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

invokeIRQHandler :: IRQHandlerInvocation -> Kernel ()
invokeIRQHandler (AckIRQ irq) =
    doMachineOp (if config_ARM_GIC_V3
                 then deactivateInterrupt (theIRQ irq)
                 else maskInterrupt False irq)
invokeIRQHandler _ = return ()

handleReservedIRQ :: IRQ -> Kernel ()
handleReservedIRQ irq = do
    when (fromEnum irq == fromEnum irqVGICMaintenance) vgicMaintenance
    when (irqVPPIEventIndex irq /= Nothing) $ vppiEvent irq
    return ()

maskIrqSignal :: IRQ -> Kernel ()
maskIrqSignal irq =
    when (not config_ARM_GIC_V3) (doMachineOp $ maskInterrupt True irq)

initInterruptController :: Kernel ()
initInterruptController = error "Unimplemented. Init code."

-- This check takes a different form on architectures where the invalid IRQ is
-- in the [minIRQ,maxIRQ] range. On Arm platforms, irqInvalid is outside
-- that range, hence the rangeCheck implicitly checks for irqInvalid
checkIRQ :: Word -> KernelF SyscallError ()
checkIRQ irq = rangeCheck irq (fromEnum minIRQ) (fromEnum maxIRQ)
