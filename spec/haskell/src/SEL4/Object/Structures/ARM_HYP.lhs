%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module contains the physical memory model's representations of the ARM-specific data structures, as well as a type representing a capability to an ARM-specific object.

\begin{impdetails}

This module makes use of the GHC extension allowing declaration of types with no constructors, so GHC language extensions are enabled.

> {-# LANGUAGE CPP, EmptyDataDecls, GeneralizedNewtypeDeriving #-}

\end{impdetails}

> module SEL4.Object.Structures.ARM_HYP where

\begin{impdetails}

> import SEL4.Machine.RegisterSet
> import SEL4.Machine.Hardware.ARM_HYP
> import Data.Array
> import Data.Word(Word32,Word16)
> import Data.Bits
> import {-# SOURCE #-} SEL4.Object.VCPU.ARM_HYP (VCPU())

\end{impdetails}

\subsection{Capabilities}

There are six ARM-specific capability types: the global ASID control capability, ASID pools, page tables, page directories, and pages.

> data ArchCapability
>     = ASIDPoolCap {
>         capASIDPool :: PPtr ASIDPool,
>         capASIDBase :: ASID }
>     | ASIDControlCap
>     | PageCap {
>         capVPBasePtr :: PPtr Word,
>         capVPRights :: VMRights,
>         capVPSize :: VMPageSize,
>         capVPisIOSpace :: Bool,
>         capVPMappedAddress :: Maybe (ASID, VPtr) }
>     | PageTableCap {
>         capPTBasePtr :: PPtr PTE,
>         capPTMappedAddress :: Maybe (ASID, VPtr) }
>     | PageDirectoryCap {
>         capPDBasePtr :: PPtr PDE,
>         capPDMappedASID :: Maybe ASID }
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     | VCPUCap {
>         capVCPUPtr :: PPtr VCPU }
#endif
#ifdef CONFIG_ARM_SMMU
>     | IOSpaceCap {
>         capIOSpaceModuleID :: Word16,
>         capIOSpaceClientID :: Word16 }
>     | IOPageTableCap {
>         capIOPTBasePtr :: PPtr IOPTE,
>         capIOPTMappedAddress :: Maybe (ASID, VPtr) }
#endif
>     deriving (Eq, Show)

\subsection{Kernel Objects}

The ARM kernel stores some ARM-specific types of objects in the PSpace, such as ASID pools, which are second level nodes in the global ASID table.

> data ArchKernelObject
>     = KOASIDPool ASIDPool
>     | KOPTE PTE
>     | KOPDE PDE
#ifdef CONFIG_ARM_SMMU
>     | KOIOPTE IOPTE
>     | KOIOPDE IOPDE
#endif
>     deriving Show

FIXME ARMHYP add VCPU to ArchKernelObject? MAYBE

> archObjSize ::  ArchKernelObject -> Int
> archObjSize a = case a of
>                 KOASIDPool _ -> pageBits
>                 KOPTE _ -> pteBits
>                 KOPDE _ -> pdeBits
#ifdef CONFIG_ARM_SMMU
>                 KOIOPTE _ -> iopteBits
>                 KOIOPDE _ -> iopdeBits
#endif

\subsection{ASID Pools}

An ASID pool is an array of pointers to page directories. This is used to implement virtual ASIDs on ARM; it is not accessed by the hardware.

> newtype ASIDPool = ASIDPool (Array ASID (Maybe (PPtr PDE)))
>     deriving Show

An ASID is an unsigned word. Note that it is a \emph{virtual} address space identifier, and may not correspond to any hardware-defined identifier --- especially on ARMv5 and earlier, where the only identifier implemented in hardware is the 4-bit domain number.

> newtype ASID = ASID Word32
>     deriving (Show, Eq, Ord, Enum, Real, Integral, Num, Bits, Ix, Bounded)

ASIDs are mapped to address space roots by a global two-level table. The actual ASID values are opaque to the user, as are the sizes of the levels of the tables; ASID allocation calls will simply return an error once the available ASIDs are exhausted.

FIXME ARMHYP after device untyped patch this will be 6 and 7 respectively

> asidHighBits :: Int
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> asidHighBits = 7 -- isIOSpace takes away one bit
#else
> asidHighBits = 8
#endif

> asidLowBits :: Int
> asidLowBits = 10

> asidBits :: Int
> asidBits = asidHighBits + asidLowBits

> asidRange :: (ASID, ASID)
> asidRange = (0, (1 `shiftL` asidBits) - 1)

> asidHighBitsOf :: ASID -> ASID
> asidHighBitsOf asid = (asid `shiftR` asidLowBits) .&. mask asidHighBits

