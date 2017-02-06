%
% Copyright 2016, Data61, CSIRO
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(DATA61_GPL)
%

This module defines the encoding of arch-specific faults.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.API.Faults.ARM_HYP where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.TCB(asUser)
> import Data.Bits
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Machine.Hardware.ARM_HYP(addressTranslateS1CPR)
#endif

\end{impdetails}

> import SEL4.API.Failures.ARM_HYP

FIXME ARMHYP why is this code (from setMRs\_fault) duplicating the translation
in handleVMFault?

> makeArchFaultMessage :: ArchFault -> PPtr TCB -> Kernel (Word, [Word])
> makeArchFaultMessage (VMFault vptr archData) thread = do
>     pc <- asUser thread getRestartPC
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>     return (5, pc:fromVPtr vptr:archData)
#else
>     upc <- doMachineOp (addressTranslateS1CPR $ VPtr pc)
>     let faddr = (upc .&. complement (mask pageBits)) .|.
>                 (VPtr pc .&. mask pageBits)
>     return (5, fromVPtr faddr:fromVPtr vptr:archData)
#endif
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> makeArchFaultMessage (VCPUFault hsr) thread = return (7, [hsr])
> makeArchFaultMessage (VGICMaintenance archData) thread = do
>     return (6, archData) -- FIXME ARMHYP check vgic index here?
#endif

> handleArchFaultReply :: ArchFault -> PPtr TCB -> Word -> [Word] -> Kernel Bool
> handleArchFaultReply (VMFault {}) _ _ _ = return True
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> handleArchFaultReply (VCPUFault {}) _ _ _ = return True
> handleArchFaultReply (VGICMaintenance {}) _ _ _ = return True
#endif

