%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines the machine-specific interrupt handling routines.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.Interrupt.ARM_HYP where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.API.Failures
> import SEL4.API.Invocation.ARM_HYP as ArchInv
> import {-# SOURCE #-} SEL4.Object.Interrupt (setIRQState)

\end{impdetails}

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Machine.Hardware.ARM_HYP.PLATFORM (irqVGICMaintenance, irqSMMU)
#endif

> decodeIRQControlInvocation :: Word -> [Word] -> PPtr CTE -> [Capability] ->
>     KernelF SyscallError ArchInv.IRQControlInvocation
> decodeIRQControlInvocation _ _ _ _ = throw IllegalOperation

> performIRQControl :: ArchInv.IRQControlInvocation -> KernelP ()
> performIRQControl _ = fail "performIRQControl: not defined"

> checkIRQ :: Word -> KernelF SyscallError ()
> checkIRQ irq = rangeCheck irq (fromEnum minIRQ) (fromEnum maxIRQ)

FIXME ARMHYP INTERRUPT_VGIC_MAINTENANCE and INTERRUPT_SMMU

> handleReservedIRQ :: IRQ -> Kernel ()
> handleReservedIRQ irq = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     fail "FIXME ARMHYP handleReservedIRQ"
#else
>     return () -- handleReservedIRQ does nothing on ARM
#endif

> initInterruptController :: Kernel ()
> initInterruptController = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     setIRQState IRQReserved $ IRQ irqVGICMaintenance
#endif
#ifdef CONFIG_SMMU
>     setIRQState IRQReserved $ IRQ irqSMMU
#endif
>     return ()

