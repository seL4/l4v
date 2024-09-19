%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains the architecture-specific thread switch code for X86-64bit.

> module SEL4.Kernel.Thread.X64 where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Model.StateData
> import SEL4.Object.Structures
> import SEL4.Kernel.VSpace.X64
> import {-# SOURCE #-} SEL4.Kernel.Init
> import SEL4.Object.FPU.X64

\end{impdetails}

> switchToThread :: PPtr TCB -> Kernel ()
> switchToThread tcb = do
>     setVMRoot tcb
>     lazyFpuRestore tcb

> configureIdleThread :: PPtr TCB -> KernelInit ()
> configureIdleThread _ = error "Unimplemented. init code"

> switchToIdleThread :: Kernel ()
> switchToIdleThread = do
>     t <- getIdleThread
>     setVMRoot t

> activateIdleThread :: PPtr TCB -> Kernel ()
> activateIdleThread _ = return ()

> prepareNextDomain :: Kernel ()
> prepareNextDomain = switchLocalFpuOwner Nothing
