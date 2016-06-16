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

\end{impdetails}

\subsection{Capabilities}

There are six ARM-specific capability types: the global ASID control capability, ASID pools, page tables, page directories, and pages.

FIXME ARMHYP frame caps in C have an isIOSpace property - add this here, or add a separate PageIOCap (IOPageCap?) that simply encodes / decodes to the right thing?

> data ArchCapability
>     = ASIDPoolCap {
>         capASIDPool :: PPtr ASIDPool,
>         capASIDBase :: ASID }
>     | ASIDControlCap
>     | PageCap {
>         capVPBasePtr :: PPtr Word,
>         capVPRights :: VMRights,
>         capVPSize :: VMPageSize,
>         capVPMappedAddress :: Maybe (ASID, VPtr) }
>     | PageTableCap {
>         capPTBasePtr :: PPtr PTE,
>         capPTMappedAddress :: Maybe (ASID, VPtr) }
>     | PageDirectoryCap {
>         capPDBasePtr :: PPtr PDE,
>         capPDMappedASID :: Maybe ASID }
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     | VCPUCap {
>         capVCPUPtr :: VCPU }
#endif
#ifdef CONFIG_ARM_SMMU
>     | IOSpaceCap {
>         capIOSpaceModuleID :: Word16,
>         capIOSpaceClientID :: Word16 }
>     | IOPageDirectoryCap {
>         capIOPDBasePtr :: PPtr IOPDE,
>         capIOPDMappedAddress :: Maybe (ASID) } -- FIXME ARMHYP where is mapped address?
>     | IOPageTableCap {
>         capIOPTBasePtr :: PPtr IOPTE,
>         capIOPTMappedAddress :: Maybe (ASID, VPtr) } -- FIXME ARMHYP Vptr or PAddr?
#endif
>     deriving (Eq, Show)

\subsection{Kernel Objects}

The ARM kernel stores one ARM-specific type of object in the PSpace: ASID pools, which are second level nodes in the global ASID table.

FIXME ARMHYP how does the above comment possibly relate to the ArchKernelObject datatype?

> data ArchKernelObject
>     = KOASIDPool ASIDPool
>     | KOPTE PTE
>     | KOPDE PDE
>     deriving Show

FIXME ARMHYP add IOPTE and IOPDE to ArchKernelObject?

> archObjSize ::  ArchKernelObject -> Int
> archObjSize a = case a of
>                 KOASIDPool _ -> pageBits
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>                 KOPTE _ -> 2
>                 KOPDE _ -> 2
#else
>                 KOPTE _ -> 3
>                 KOPDE _ -> 3
#endif

\subsection{ASID Pools}

An ASID pool is an array of pointers to page directories. This is used to implement virtual ASIDs on ARM; it is not accessed by the hardware.

> newtype ASIDPool = ASIDPool (Array ASID (Maybe (PPtr PDE)))
>     deriving Show

An ASID is an unsigned word. Note that it is a \emph{virtual} address space identifier, and may not correspond to any hardware-defined identifier --- especially on ARMv5 and earlier, where the only identifier implemented in hardware is the 4-bit domain number.

> newtype ASID = ASID Word32
>     deriving (Show, Eq, Ord, Enum, Real, Integral, Num, Bits, Ix, Bounded)

ASIDs are mapped to address space roots by a global two-level table. The actual ASID values are opaque to the user, as are the sizes of the levels of the tables; ASID allocation calls will simply return an error once the available ASIDs are exhausted.

FIXME ARMHYP unclear if bit manipulation still correct

> asidHighBits :: Int
> asidHighBits = 8

> asidLowBits :: Int
> asidLowBits = 10

> asidBits :: Int
> asidBits = asidHighBits + asidLowBits

> asidRange :: (ASID, ASID)
> asidRange = (0, (1 `shiftL` asidBits) - 1)

> asidHighBitsOf :: ASID -> ASID
> asidHighBitsOf asid = (asid `shiftR` asidLowBits) .&. mask asidHighBits

