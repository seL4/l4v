%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

\begin{impdetails}

> {-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

\end{impdetails}

This module contains the architecture-specific thread switch code for the ARM.

> module SEL4.Kernel.Thread.ARM where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Machine.RegisterSet.ARM (Register(..))
> import SEL4.Model.StateData
> import SEL4.Model.PSpace (getObject)
> import SEL4.Object.Structures
> import SEL4.Object.TCB
> import SEL4.Kernel.VSpace.ARM
> import qualified SEL4.Machine.Hardware.ARM as ARMHardware
> import {-# SOURCE #-} SEL4.Kernel.Init
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Object.VCPU.ARM
#endif

\end{impdetails}

The ARM thread switch function invalidates all caches and the TLB, and writes the IPC buffer pointer to the first word of the globals page.

> switchToThread :: PPtr TCB -> Kernel ()
> switchToThread tcb = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     tcbobj <- getObject tcb
>     vcpuSwitch (atcbVCPUPtr $ tcbArch tcbobj)
#endif
>     setVMRoot tcb
>     doMachineOp $ ARMHardware.clearExMonitor

The ARM idle thread runs in system mode with interrupts enabled, with the PC pointing to a small kernel routine that executes a wait-for-interrupt instruction. In the Haskell model, this routine is placed in the globals page, so the simulator can access it; in a real kernel there would be no need for it to be user-accessible.

> configureIdleThread :: PPtr TCB -> KernelInit ()
> configureIdleThread tcb = do
>     doKernelOp $ asUser tcb $ do
>         setRegister (Register CPSR) 0x1f
>         setRegister (Register NextIP) $ fromVPtr idleThreadStart

When switching to the idle thread, we ensure that it runs in the address space of the kernel to prevent the possibility of a user-level address space being deleted whilst the idle thread is running (which is possible in a multi-core scenario).

> switchToIdleThread :: Kernel ()
> switchToIdleThread = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>    vcpuSwitch Nothing
#endif
>    t <- getIdleThread
>    setVMRoot t

There is nothing special about idle thread activation on ARM.

> activateIdleThread :: PPtr TCB -> Kernel ()
> activateIdleThread _ = return ()

There is nothing special that needs to be done before calling nextDomain on ARM.

> prepareNextDomain :: Kernel ()
> prepareNextDomain =
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>    vcpuFlush
#else
>    return ()
#endif
