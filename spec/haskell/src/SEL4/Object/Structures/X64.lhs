%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains the physical memory model's representations of the x64-specific data structures, as well as a type representing a capability to an x64-specific object.

\begin{impdetails}

This module makes use of the GHC extension allowing declaration of types with no constructors, so GHC language extensions are enabled.

> {-# LANGUAGE EmptyDataDecls, GeneralizedNewtypeDeriving #-}

\end{impdetails}

> module SEL4.Object.Structures.X64 where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine.RegisterSet
> import SEL4.Machine.Hardware.X64
> import Data.Array
> import Data.Bits
> import Data.Word(Word64)

\end{impdetails}

> --newtype IOASID = IOASID Word16
> --    deriving (Show, Eq, Ord, Enum, Real, Integral, Num, Bits, Ix, Bounded) -}

\subsection{Capabilities}

> data ArchCapability
>     = ASIDPoolCap {
>         capASIDPool :: PPtr ASIDPool,
>         capASIDBase :: ASID }
>     | ASIDControlCap
>     | IOPortCap {
>         capIOPortFirstPort :: IOPort,
>         capIOPortLastPort :: IOPort }
>     | IOPortControlCap
>--     | IOSpaceCap {
>--         capIODomainID :: Word16,
>--         capIOPCIDevice :: Maybe IOASID }
>--     | IOPageTableCap {
>--         capIOPTBasePtr :: PPtr IOPTE,
>--         capIOPTLevel :: Int,
>--         capIOPTMappedAddress :: Maybe (IOASID, VPtr) }
>     | PageCap {
>         capVPBasePtr :: PPtr Word,
>         capVPRights :: VMRights,
>         capVPMapType :: VMMapType,
>         capVPSize :: VMPageSize,
>         capVPIsDevice :: Bool,
>         capVPMappedAddress :: Maybe (ASID, VPtr) }
>     | PageTableCap {
>         capPTBasePtr :: PPtr PTE,
>         capPTMappedAddress :: Maybe (ASID, VPtr) }
>     | PageDirectoryCap {
>         capPDBasePtr :: PPtr PDE,
>         capPDMappedAddress :: Maybe (ASID, VPtr) }
>     | PDPointerTableCap {
>         capPDPTBasePtr :: PPtr PDPTE,
>         capPDPTMappedAddress :: Maybe (ASID, VPtr) }
>     | PML4Cap {
>         capPML4BasePtr :: PPtr PML4E,
>         capPML4MappedASID :: Maybe ASID }
>     deriving (Eq, Show)

The range of allowable sizes for Untyped objects depends on addressable memory
size.

> minUntypedSizeBits :: Int
> minUntypedSizeBits = 4

> maxUntypedSizeBits :: Int
> maxUntypedSizeBits = 47

\subsection{Kernel Objects}

> data ArchKernelObject
>     = KOASIDPool ASIDPool
>     | KOPTE PTE
>     | KOPDE PDE
>     | KOPDPTE PDPTE
>     | KOPML4E PML4E
>--    | KOIOPTE IOPTE
>--    | KOIORTE IORTE
>--    | KOIOCTE IOCTE
>     deriving Show

> archObjSize ::  ArchKernelObject -> Int
> archObjSize a = case a of
>                 KOASIDPool _ -> pageBits
>                 KOPTE _ -> 3
>                 KOPDE _ -> 3
>                 KOPDPTE _ -> 3
>                 KOPML4E _ -> 3
>--                KOIOPTE _ -> 3
>--                KOIOCTE _ -> 3
>--                KOIORTE _ -> 3 -- FIXME: Not correct ?

\subsection{Threads}

TCBs contain state that is arch-specific. ``ArchTCB'' represents a wrapper for
this state. The thread's saved user-level context, which is expected to be
present on all platforms is stored here.

> data ArchTCB = ArchThread {
>         atcbContext :: UserContext }
>     deriving Show

> newArchTCB = ArchThread {
>     atcbContext = newContext }

> atcbContextSet :: UserContext -> ArchTCB -> ArchTCB
> atcbContextSet uc atcb = atcb { atcbContext = uc }
>
> atcbContextGet :: ArchTCB -> UserContext
> atcbContextGet = atcbContext

> data ArchTcbFlag = FpuDisabled

> archTcbFlagToWord :: ArchTcbFlag -> Word
> archTcbFlagToWord (FpuDisabled) = bit 0

\subsection{ASID Pools}

An ASID pool is an array of pointers to page directories. This is used to implement virtual ASIDs on x64; it is not accessed by the hardware.

> newtype ASIDPool = ASIDPool (Array ASID (Maybe (PPtr PML4E)))
>     deriving Show

An ASID is an unsigned word. Note that it is a \emph{virtual} address space identifier, and does not correspond to any hardware-defined identifier.

> newtype ASID = ASID { fromASID :: Word64 }
>     deriving (Show, Eq, Ord, Enum, Real, Integral, Num, Bits, Ix, Bounded)

ASIDs are mapped to address space roots by a global two-level table. The actual ASID values are opaque to the user, as are the sizes of the levels of the tables; ASID allocation calls will simply return an error once the available ASIDs are exhausted.

> asidHighBits :: Int
> asidHighBits = 3

> asidLowBits :: Int
> asidLowBits = 9

> asidBits :: Int
> asidBits = asidHighBits + asidLowBits

> asidRange :: (ASID, ASID)
> asidRange = (0, (1 `shiftL` asidBits) - 1)

> asidHighBitsOf :: ASID -> ASID
> asidHighBitsOf asid = (asid `shiftR` asidLowBits) .&. mask asidHighBits

> asidLowBitsOf :: ASID -> ASID
> asidLowBitsOf asid = asid .&. mask asidLowBits

> data CR3 = CR3 {
>     cr3BaseAddress :: PAddr,
>     cr3pcid :: ASID }
>     deriving (Show, Eq)

> makeCR3 :: PAddr -> ASID -> CR3
> makeCR3 vspace asid = CR3 vspace' asid
>     where
>         vspace' = vspace .&. (mask pml4ShiftBits `shiftL` asidBits)

\subsection{IRQ State}

> data X64IRQState =
>     X64IRQFree
>   | X64IRQReserved
>   | X64IRQMSI {
>     msiBus :: Word,
>     msiDev :: Word,
>     msiFunc :: Word,
>     msiHandle :: Word }
>   | X64IRQIOAPIC {
>     irqIOAPIC :: Word,
>     irqPin :: Word,
>     irqLevel :: Word,
>     irqPolarity :: Word,
>     irqMasked :: Bool }

