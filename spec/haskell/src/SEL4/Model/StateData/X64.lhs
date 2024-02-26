%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains the architecture-specific kernel global data for the X86-64bit architecture.

> module SEL4.Model.StateData.X64 where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Machine.Hardware.X64 (PML4E(..),PDPTE(..),PDE(..),PTE(..),IOPort)
> import SEL4.Object.Structures.X64

> import Data.Array
> import Data.Word(Word8)

\end{impdetails}

%FIXME x64: potential C bug: the gdt entry structure in C only has 32 bits for addresses

> data X64VSpaceRegionUse
>  = X64VSpaceUserRegion
>  | X64VSpaceInvalidRegion
>  | X64VSpaceKernelWindow
>  | X64VSpaceDeviceWindow


> gdteBits :: Int
> gdteBits = 3

> data KernelState = X64KernelState {
>     x64KSASIDTable        :: Array ASID (Maybe (PPtr ASIDPool)),
>     x64KSSKIMPML4         :: PPtr PML4E,
>     x64KSSKIMPDPTs        :: [PPtr PDPTE],
>     x64KSSKIMPDs          :: [PPtr PDE],
>     x64KSSKIMPTs          :: [PPtr PTE],
>     x64KSCurrentUserCR3   :: CR3,
>     x64KSKernelVSpace     :: PPtr Word -> X64VSpaceRegionUse,
>     x64KSAllocatedIOPorts :: Array IOPort Bool,
>     x64KSNumIOAPICs       :: Word,
>     x64KSIOAPICnIRQs      :: Word -> Word8,
>     x64KSIRQState         :: Array IRQ X64IRQState}

> newKernelState :: PAddr -> (KernelState, [PAddr])
> newKernelState _ = error "No initial state defined for x64"
