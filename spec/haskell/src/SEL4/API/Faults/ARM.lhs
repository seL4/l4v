%
% Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the encoding of arch-specific faults.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.API.Faults.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.TCB(asUser)
> import Data.Bits
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Machine.Hardware.ARM(addressTranslateS1)
#endif

\end{impdetails}

> import SEL4.API.Failures.ARM

FIXME ARMHYP why is this code (from setMRs\_fault) duplicating the translation
in handleVMFault?

> makeArchFaultMessage :: ArchFault -> PPtr TCB -> Kernel (Word, [Word])
> makeArchFaultMessage (VMFault vptr archData) thread = do
>     pc <- asUser thread getRestartPC
>     return (5, pc:fromVPtr vptr:archData)
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> makeArchFaultMessage (VCPUFault hsr) thread = return (7, [hsr])
> makeArchFaultMessage (VPPIEvent irq) thread = return (8, [fromIntegral $ fromEnum $ irq])
> makeArchFaultMessage (VGICMaintenance archData) thread = do
>     let msg = (case archData of
>                    Nothing -> [-1]
>                    Just idx -> [idx])
>     return (6, msg)
#endif

> handleArchFaultReply :: ArchFault -> PPtr TCB -> Word -> [Word] -> Kernel Bool
> handleArchFaultReply (VMFault {}) _ _ _ = return True
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> handleArchFaultReply (VCPUFault {}) _ _ _ = return True
> handleArchFaultReply (VPPIEvent {}) _ _ _ = return True
> handleArchFaultReply (VGICMaintenance {}) _ _ _ = return True
#endif

