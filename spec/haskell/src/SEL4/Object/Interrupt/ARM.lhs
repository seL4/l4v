%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the machine-specific interrupt handling routines.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.Interrupt.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.API.Failures
> import SEL4.API.Types
> import SEL4.API.InvocationLabels
> import SEL4.API.Invocation
> import SEL4.API.Invocation.ARM as ArchInv
> import SEL4.API.InvocationLabels.ARM as ArchLabels
> import SEL4.Machine.Hardware.ARM (config_ARM_GIC_V3, deactivateInterrupt)
> import {-# SOURCE #-} SEL4.Object.Interrupt (setIRQState, isIRQActive)
> import {-# SOURCE #-} SEL4.Kernel.CSpace
> import {-# SOURCE #-} SEL4.Object.CNode
> import qualified SEL4.Machine.Hardware.ARM as Arch
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Object.VCPU.TARGET (vgicMaintenance, vppiEvent, irqVPPIEventIndex)
> import SEL4.Machine.Hardware.ARM.PLATFORM (irqVGICMaintenance, irqVTimerEvent, irqSMMU)
#endif

\end{impdetails}


> decodeIRQControlInvocation :: Word -> [Word] -> PPtr CTE -> [Capability] ->
>         KernelF SyscallError ArchInv.IRQControlInvocation
> decodeIRQControlInvocation label args srcSlot extraCaps =
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel ArchLabels.ARMIRQIssueIRQHandler, irqW:triggerW:index:depth:_, cnode:_) -> do
>             checkIRQ irqW
>             let irq = toEnum (fromIntegral irqW) :: IRQ
>             irqActive <- withoutFailure $ isIRQActive irq
>             when irqActive $ throw RevokeFirst
>
>             destSlot <- lookupTargetSlot cnode
>                 (CPtr index) (fromIntegral depth)
>             ensureEmptySlot destSlot
>             return $ ArchInv.IssueIRQHandler irq destSlot srcSlot (triggerW /= 0)
>         (ArchInvocationLabel ArchLabels.ARMIRQIssueIRQHandler,_,_) -> throw TruncatedMessage
>         _ -> throw IllegalOperation

> performIRQControl :: ArchInv.IRQControlInvocation -> KernelP ()
> performIRQControl (ArchInv.IssueIRQHandler (IRQ irq) destSlot srcSlot trigger) = withoutPreemption $ do
>     doMachineOp $ Arch.setIRQTrigger irq trigger
>     -- do same thing as generic path in performIRQControl in Interrupt.lhs
>     setIRQState IRQSignal (IRQ irq)
>     cteInsert (IRQHandlerCap (IRQ irq)) srcSlot destSlot
>     return ()

> invokeIRQHandler :: IRQHandlerInvocation -> Kernel ()
> invokeIRQHandler (AckIRQ irq) =
>     doMachineOp (if config_ARM_GIC_V3
>                  then deactivateInterrupt (theIRQ irq)
>                  else maskInterrupt False irq)
> invokeIRQHandler _ = return ()

> maskIrqSignal :: IRQ -> Kernel ()
> maskIrqSignal irq =
>     when (not config_ARM_GIC_V3) (doMachineOp $ maskInterrupt True irq)

> checkIRQ :: Word -> KernelF SyscallError ()
> checkIRQ irq = rangeCheck irq (fromEnum minIRQ) (fromEnum maxIRQ)

> handleReservedIRQ :: IRQ -> Kernel ()
> handleReservedIRQ irq = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     when (fromEnum irq == fromEnum irqVGICMaintenance) vgicMaintenance
>     when (irqVPPIEventIndex irq /= Nothing) $ vppiEvent irq
>     return ()
#else
>     return () -- handleReservedIRQ does nothing on ARM
#endif

> initInterruptController :: Kernel ()
> initInterruptController = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     setIRQState IRQReserved $ IRQ irqVGICMaintenance
>     setIRQState IRQReserved $ IRQ irqVTimerEvent
#endif
#ifdef CONFIG_SMMU
>     setIRQState IRQReserved $ IRQ irqSMMU
#endif
>     return ()

