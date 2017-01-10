% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module contains the architecture-specific thread switch code for X86-64bit.

> module SEL4.Kernel.Thread.X64 where

\begin{impdetails}

> import SEL4.Machine
> import qualified SEL4.Machine.RegisterSet.X64 as ArchReg
> import SEL4.Model.StateData
> import SEL4.Model.StateData.X64
> import SEL4.Object.Structures
> import SEL4.Object.TCB
> import SEL4.Kernel.VSpace.X64
> import qualified SEL4.Machine.Hardware.X64 as Arch
> import {-# SOURCE #-} SEL4.Kernel.Init
> import Data.Array
> import Data.Bits

\end{impdetails}

> switchToThread :: PPtr TCB -> Kernel ()
> switchToThread tcb = setVMRoot tcb

> configureIdleThread :: PPtr TCB -> KernelInit ()
> configureIdleThread _ = error "Unimplemented. init code"

> switchToIdleThread :: Kernel ()
> switchToIdleThread = return ()

> activateIdleThread :: PPtr TCB -> Kernel ()
> activateIdleThread _ = return ()

