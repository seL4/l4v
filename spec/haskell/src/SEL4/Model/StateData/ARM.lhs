%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains the architecture-specific kernel global data for the ARM architecture.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Model.StateData.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Machine.Hardware.ARM
>     (HardwareASID(..), PTE(..), PDE(..), ptBits, pdBits)
> import SEL4.Object.Structures.ARM

> import Data.Array
> import Data.Bits
> import Data.Helpers

\end{impdetails}

The datatype ArmVSpaceRegionUse is solely used to formulate invariants about the use of memory regions.
Consider the data to be ghost state (only written, never read by the implementation).

> data ArmVSpaceRegionUse
>  = ArmVSpaceUserRegion
>  | ArmVSpaceInvalidRegion
>  | ArmVSpaceKernelWindow
>  | ArmVSpaceDeviceWindow

There are three ARM-specific global data elements:

\begin{itemize}
\item a pointer to the globals frame, which is used to map thread-local data --- such as the IPC buffer location --- into every user thread's address space;
\item the root ASID table; and
\item the global page directory, which is copied to initialise new page directories, and also as the hardware page table root when the current thread has no valid root.
\end{itemize}

seL4 stores the hardware ASID into the last (invalid) entry of a page
directory, which the user cannot map. This allows fast changes to hardware
ASIDs for a given address space.  To represent this, we use a ghost state
armKSASIDMap to map from page directories to hardware ASIDs.

armKSKernelVSpace is ghost state.

FIXME ARMHYP_SMMU ARMHYP missing IO ASID to PD map for SMMU

> data KernelState = ARMKernelState {
>     armKSASIDTable :: Array ASID (Maybe (PPtr ASIDPool)),
>     armKSHWASIDTable :: Array HardwareASID (Maybe ASID),
>     armKSNextASID :: HardwareASID,
>     armKSASIDMap :: Array ASID (Maybe (HardwareASID, PPtr PDE)),
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>     armKSGlobalPD :: PPtr PDE,
>     armKSGlobalPTs :: [PPtr PTE],
#else
>     armHSCurVCPU :: Maybe (PPtr VCPU, Bool),
>     armKSGICVCPUNumListRegs :: Int,
>     armUSGlobalPD :: PPtr PDE,
>     -- a page directory containing invalid mappings (no shared kernel region)
#endif
>     armKSKernelVSpace :: PPtr Word -> ArmVSpaceRegionUse}

#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT

> newKernelState :: PAddr -> (KernelState, [PAddr])
> newKernelState data_start = (state, frames)
>     where
>         alignToBits addr b = (((addr - 1) `shiftR` b) + 1) `shiftL` b
>         globalsFrame = data_start `alignToBits` pageBits
>         globalsFrameTop = globalsFrame + bit pageBits
>         globalPTs = globalsFrameTop `alignToBits` pageBits
>         globalPTsTop = globalPTs + bit pageBits
>         globalPD = globalPTsTop `alignToBits` pdBits
>         globalPDTop = globalPD + bit pdBits
>         frames = globalsFrame :
>             [globalPTs, globalPTs + bit pageBits .. globalPTsTop - 1] ++
>             [globalPD, globalPD + bit pageBits .. globalPDTop - 1]
>         state = ARMKernelState {
>             armKSASIDTable = funPartialArray (const Nothing) (0, (1 `shiftL` asidHighBits) - 1),
>             armKSHWASIDTable = funArray (const Nothing),
>             armKSNextASID = minBound,
>             armKSASIDMap = funPartialArray (const Nothing) asidRange,
>             armKSGlobalPD = ptrFromPAddr globalPD,
>             armKSGlobalPTs = map ptrFromPAddr
>                 [globalPTs, globalPTs + bit ptBits .. globalPTsTop-1],
>             armKSKernelVSpace =
>                 (\vref -> if vref < mask 20 then ArmVSpaceKernelWindow
>                                             else ArmVSpaceInvalidRegion) }

#else /* CONFIG_ARM_HYPERVISOR_SUPPORT */

FIXME ARMHYP what is this thing, what is data_start? where is it getting data_start? what are these frames it is returning?

FIXME ARMHYP not even sure if mask 20 is correct here

FIXME ARMHYP ok, someone needs to explain how this actually works before it gets fixed

> newKernelState :: PAddr -> (KernelState, [PAddr])
> newKernelState data_start = (state, frames)
>     where
>         alignToBits addr b = (((addr - 1) `shiftR` b) + 1) `shiftL` b
>         globalsFrame = data_start `alignToBits` pageBits
>         globalsFrameTop = globalsFrame + bit pageBits
>         frames = error "FIXME ARMHYP TODO"
>         state = ARMKernelState {
>             armKSASIDTable = funPartialArray (const Nothing) (0, (1 `shiftL` asidHighBits) - 1),
>             armKSHWASIDTable = funArray (const Nothing),
>             armKSNextASID = minBound,
>             armKSASIDMap = funPartialArray (const Nothing) asidRange,
>             armHSCurVCPU = Nothing,
>             armKSGICVCPUNumListRegs = error "FIXME ARMHYP read from platform",
>             armUSGlobalPD = error "FIXME ARMHYP address of C global constant",
>             armKSKernelVSpace =
>                 (\vref -> if vref < mask 20 then ArmVSpaceKernelWindow
>                                             else ArmVSpaceInvalidRegion)
>             }

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

