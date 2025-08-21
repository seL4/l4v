%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the machine-specific interrupt handling routines for x64.

> {-# LANGUAGE CPP #-}

> module SEL4.Object.Interrupt.X64 where


\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Model.StateData.X64
> import SEL4.Object.Structures
> import SEL4.API.Failures
> import SEL4.API.Types
> import SEL4.API.Invocation
> import SEL4.API.InvocationLabels
> import SEL4.API.Invocation.X64 as ArchInv
> import SEL4.API.InvocationLabels.X64 as ArchLabels
> import {-# SOURCE #-} SEL4.Object.CNode
> import {-# SOURCE #-} SEL4.Kernel.CSpace
> import {-# SOURCE #-} SEL4.Object.Interrupt
> import qualified SEL4.Machine.Hardware.X64 as Arch
> import Data.Word (Word8)
> import Data.Array ((//))
> import Data.Bits


\end{impdetails}

%FIXME: argument order, IRQ shouldn't be last. Fix in C.

%FIXME: remove duplication with decodeIRQControl, move code to generic case. Do this on C first.

> decodeIRQControlInvocation :: Word -> [Word] -> PPtr CTE -> [Capability] ->
>         KernelF SyscallError ArchInv.IRQControlInvocation
> decodeIRQControlInvocation label args srcSlot extraCaps =
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel ArchLabels.X64IRQIssueIRQHandlerIOAPIC,
>                  index:depth:ioapic:pin:level:polarity:irqW:_, cnode:_) -> do
>
>             rangeCheck irqW 0 (fromEnum Arch.maxUserIRQ - fromEnum Arch.minUserIRQ)
>             let preIrq = fromIntegral irqW :: Word8
>             let irq = toEnum (fromEnum Arch.minUserIRQ + fromIntegral preIrq) :: IRQ
>
>             irqActive <- withoutFailure $ isIRQActive irq
>             when irqActive $ throw RevokeFirst
>
>             destSlot <- lookupTargetSlot cnode (CPtr index)
>                 (fromIntegral depth)
>             ensureEmptySlot destSlot
>
>             -- from ioapic_map_pin_to_vector
>             numIOAPICs <- withoutFailure $ gets (x64KSNumIOAPICs . ksArchState)
>             ioAPICnIRQs <- withoutFailure $ gets (x64KSIOAPICnIRQs . ksArchState)
>             when (numIOAPICs == 0) $ throw IllegalOperation
>             rangeCheck ioapic 0 (numIOAPICs - 1)
>             rangeCheck pin 0 (ioAPICnIRQs ioapic - 1)
>             rangeCheck level (0::Word) 1
>             rangeCheck polarity (0::Word) 1
>
>             let vector = fromIntegral (fromEnum irq) + Arch.irqIntOffset
>             return $ ArchInv.IssueIRQHandlerIOAPIC irq destSlot srcSlot ioapic
>                 pin level polarity vector
>
>         (ArchInvocationLabel ArchLabels.X64IRQIssueIRQHandlerIOAPIC, _, _) -> throw TruncatedMessage
>
>         (ArchInvocationLabel ArchLabels.X64IRQIssueIRQHandlerMSI,
>                  index:depth:pciBus:pciDev:pciFunc:handle:irqW:_, cnode:_) -> do
>
>             rangeCheck irqW 0 (fromEnum Arch.maxUserIRQ - fromEnum Arch.minUserIRQ)
>             let preIrq = fromIntegral irqW :: Word8
>             let irq = toEnum (fromEnum Arch.minUserIRQ + fromIntegral preIrq) :: IRQ
>
>             irqActive <- withoutFailure $ isIRQActive irq
>             when irqActive $ throw RevokeFirst
>
>             destSlot <- lookupTargetSlot cnode (CPtr index)
>                 (fromIntegral depth)
>
>             ensureEmptySlot destSlot
>             rangeCheck pciBus 0 Arch.maxPCIBus
>             rangeCheck pciDev 0 Arch.maxPCIDev
>             rangeCheck pciFunc 0 Arch.maxPCIFunc
>
>             return $ ArchInv.IssueIRQHandlerMSI irq destSlot srcSlot pciBus
>                 pciDev pciFunc handle
>
>         (ArchInvocationLabel ArchLabels.X64IRQIssueIRQHandlerMSI, _, _) -> throw TruncatedMessage

>         _ -> throw IllegalOperation

updateIRQState sets the arch-specific IRQ state for an IRQ

> updateIRQState :: IRQ -> X64IRQState -> Kernel ()
> updateIRQState irq irqState = do
>     irqStates <- gets (x64KSIRQState . ksArchState)
>     modify (\s -> s { ksArchState = (ksArchState s) { x64KSIRQState = irqStates // [(irq, irqState)]} })

> performIRQControl :: ArchInv.IRQControlInvocation -> KernelP ()
> performIRQControl (ArchInv.IssueIRQHandlerIOAPIC (IRQ irq) destSlot srcSlot ioapic
>         pin level polarity vector) = withoutPreemption $ do
>     doMachineOp $ Arch.ioapicMapPinToVector ioapic pin level polarity vector
>     irqState <- return $ X64IRQIOAPIC (ioapic .&. mask 5) (pin .&. mask 5) (level .&. 1) (polarity .&. 1) True
>     updateIRQState (IRQ irq) irqState
>     -- do same thing as generic path in performIRQControl in Interrupt.lhs
>     setIRQState IRQSignal (IRQ irq)
>     cteInsert (IRQHandlerCap (IRQ irq)) srcSlot destSlot
>     return ()
>
> performIRQControl (ArchInv.IssueIRQHandlerMSI (IRQ irq) destSlot srcSlot pciBus
>         pciDev pciFunc handle) = withoutPreemption $ do
>     irqState <- return $ X64IRQMSI (pciBus .&. mask 8) (pciDev .&. mask 5) (pciFunc .&. mask 3) (handle .&. mask 32)
>     updateIRQState (IRQ irq) irqState
>     -- do same thing as generic path in performIRQControl in Interrupt.lhs
>     setIRQState IRQSignal (IRQ irq)
>     cteInsert (IRQHandlerCap (IRQ irq)) srcSlot destSlot
>     return ()

> invokeIRQHandler :: IRQHandlerInvocation -> Kernel ()
> invokeIRQHandler (AckIRQ irq) = doMachineOp $ maskInterrupt False irq
> invokeIRQHandler _ = return ()

> maskIrqSignal :: IRQ -> Kernel ()
> maskIrqSignal irq = doMachineOp $ maskInterrupt True irq

%FIXME: separate ranges for ISA interrupts and user interrupts

checkIRQ is only used for the legacy PIC interrupt so always fails with the IOAPIC of x86-64

> checkIRQ :: Word -> KernelF SyscallError ()
> checkIRQ irq = throw IllegalOperation

%FIXME: handle VTD faults

> handleSpuriousIRQ :: Kernel ()
> handleSpuriousIRQ = return ()

> handleReservedIRQ :: IRQ -> Kernel ()
> handleReservedIRQ _ = return ()

> initInterruptController :: Kernel ()
> initInterruptController = return ()

