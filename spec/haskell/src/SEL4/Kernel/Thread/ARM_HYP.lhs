%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

\begin{impdetails}

> {-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

\end{impdetails}

This module contains the architecture-specific thread switch code for the ARM.

> module SEL4.Kernel.Thread.ARM_HYP where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Machine.RegisterSet.ARM_HYP
> import SEL4.Model.StateData
> import SEL4.Object.Structures
> import SEL4.Object.TCB
> import SEL4.Kernel.VSpace.ARM_HYP
> import qualified SEL4.Machine.Hardware.ARM_HYP as ARMHardware
> import {-# SOURCE #-} SEL4.Kernel.Init
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Object.VCPU.ARM_HYP
#endif

\end{impdetails}

The ARM thread switch function invalidates all caches and the TLB, and writes the IPC buffer pointer to the first word of the globals page.

> switchToThread :: PPtr TCB -> Kernel ()
> switchToThread tcb = do
>     setVMRoot tcb
>     doMachineOp $ ARMHardware.clearExMonitor

The ARM idle thread runs in system mode with interrupts enabled, with the PC pointing to a small kernel routine that executes a wait-for-interrupt instruction. In the Haskell model, this routine is placed in the globals page, so the simulator can access it; in a real kernel there would be no need for it to be user-accessible.

> configureIdleThread :: PPtr TCB -> KernelInit ()
> configureIdleThread tcb = do
>     doKernelOp $ asUser tcb $ do
>         setRegister (Register CPSR) 0x1f
>         setRegister (Register LR_svc) $ fromVPtr idleThreadStart

Since the idle thread only accesses global mappings, there is nothing to be done when switching to it.

> switchToIdleThread :: Kernel ()
> switchToIdleThread = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>    vcpuSwitch Nothing
#else
>    return ()
#endif

There is nothing special about idle thread activation on ARM.

> activateIdleThread :: PPtr TCB -> Kernel ()
> activateIdleThread _ = return ()

