%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains the physical memory model's representations of the ARM-specific data structures, as well as a type representing a capability to an ARM-specific object.

\begin{impdetails}

This module makes use of the GHC extension allowing declaration of types with no constructors, so GHC language extensions are enabled.

> {-# LANGUAGE CPP, EmptyDataDecls, GeneralizedNewtypeDeriving #-}

\end{impdetails}

> module SEL4.Object.Structures.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine.RegisterSet
> import SEL4.Machine.Hardware.ARM
> import Data.Array
> import Data.Helpers
> import Data.Word(Word64,Word32,Word16)
> import Data.Bits
> import {-# SOURCE #-} SEL4.Object.Structures
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Machine.RegisterSet.ARM (VCPUReg(..))
#endif

\end{impdetails}

\subsection{Capabilities}

There are six ARM-specific capability types: the global ASID control capability, ASID pools, page tables, page directories, and pages.

> data ArchCapability
>     = ASIDPoolCap {
>         capASIDPool :: PPtr ASIDPool,
>         capASIDBase :: ASID }
>     | ASIDControlCap
>     | PageCap {
>         capVPIsDevice :: Bool,
>         capVPBasePtr :: PPtr Word,
>         capVPRights :: VMRights,
>         capVPSize :: VMPageSize,
#ifdef CONFIG_ARM_SMMU
>         capVPisIOSpace :: Bool,
#endif
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

The range of allowable sizes for Untyped objects depends on addressable memory
size.

> minUntypedSizeBits :: Int
> minUntypedSizeBits = 4

> maxUntypedSizeBits :: Int
> maxUntypedSizeBits = 29

\subsection{Kernel Objects}

The ARM kernel stores some ARM-specific types of objects in the PSpace, such as ASID pools, which are second level nodes in the global ASID table.

> data ArchKernelObject
>     = KOASIDPool ASIDPool
>     | KOPTE PTE
>     | KOPDE PDE
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     | KOVCPU VCPU
#endif
#ifdef CONFIG_ARM_SMMU
>     | KOIOPTE IOPTE
>     | KOIOPDE IOPDE
#endif
>     deriving Show

> archObjSize ::  ArchKernelObject -> Int
> archObjSize a = case a of
>                 KOASIDPool _ -> pageBits
>                 KOPTE _ -> pteBits
>                 KOPDE _ -> pdeBits
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>                 KOVCPU _ -> vcpuBits
#endif
#ifdef CONFIG_ARM_SMMU
>                 KOIOPTE _ -> iopteBits
>                 KOIOPDE _ -> iopdeBits
#endif

\subsection{Threads}

TCBs contain state that is arch-specific. ``ArchTCB'' represents a wrapper for
this state. The thread's saved user-level context, which is expected to be
present on all platforms is stored here.

> data ArchTCB = ArchThread {
>         atcbContext :: UserContext
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>         ,atcbVCPUPtr :: Maybe (PPtr VCPU)
#endif
>         }
>     deriving Show

> newArchTCB = ArchThread {
>     atcbContext = newContext
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     ,atcbVCPUPtr = Nothing
#endif
>     }

> atcbContextSet :: UserContext -> ArchTCB -> ArchTCB
> atcbContextSet uc atcb = atcb { atcbContext = uc }
>
> atcbContextGet :: ArchTCB -> UserContext
> atcbContextGet = atcbContext

\subsection{ASID Pools}

An ASID pool is an array of pointers to page directories. This is used to implement virtual ASIDs on ARM; it is not accessed by the hardware.

> newtype ASIDPool = ASIDPool (Array ASID (Maybe (PPtr PDE)))
>     deriving Show

An ASID is an unsigned word. Note that it is a \emph{virtual} address space identifier, and may not correspond to any hardware-defined identifier --- especially on ARMv5 and earlier, where the only identifier implemented in hardware is the 4-bit domain number.

> newtype ASID = ASID Word32
>     deriving (Show, Eq, Ord, Enum, Real, Integral, Num, Bits, Ix, Bounded)

ASIDs are mapped to address space roots by a global two-level table. The actual ASID values are opaque to the user, as are the sizes of the levels of the tables; ASID allocation calls will simply return an error once the available ASIDs are exhausted.

> asidHighBits :: Int
#ifdef CONFIG_ARM_SMMU
> asidHighBits = 6 -- isIOSpace takes away one bit
#else
> asidHighBits = 7
#endif

> asidLowBits :: Int
> asidLowBits = 10

> asidBits :: Int
> asidBits = asidHighBits + asidLowBits

> asidRange :: (ASID, ASID)
> asidRange = (0, (1 `shiftL` asidBits) - 1)

> asidHighBitsOf :: ASID -> ASID
> asidHighBitsOf asid = (asid `shiftR` asidLowBits) .&. mask asidHighBits

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
\subsection {VCPU}

> type VIRQ = Word

> data GICVCPUInterface = VGICInterface {
>                        vgicHCR :: Word,
>                        vgicVMCR :: Word, -- FIXME ARMHYP UNUSED?
>                        vgicAPR :: Word,
>                        vgicLR :: Array Int VIRQ
>                        }
>     deriving Show

> data VirtTimer = VirtTimer { vtimerLastPCount :: Word64 }
>     deriving Show

> data VPPIEventIRQ = VPPIEventIRQ_VTimer
>     deriving (Eq, Enum, Bounded, Ord, Ix, Show)

> data VCPU = VCPUObj {
>                 vcpuTCBPtr :: Maybe (PPtr TCB)
>                 ,vcpuVGIC :: GICVCPUInterface
>                 ,vcpuRegs :: Array VCPUReg Word
>                 ,vcpuVPPIMasked :: Array VPPIEventIRQ Bool
>                 ,vcpuVTimer :: VirtTimer
>                 }
>     deriving Show

> vcpuSCTLR vcpu = vcpuRegs vcpu ! VCPURegSCTLR

makeObject specialised to VCPUs.

> makeVCPUObject :: VCPU
> makeVCPUObject =
>     let vgicLR = funPartialArray (const (0 :: Word)) (0, gicVCPUMaxNumLR-1) in
>     VCPUObj {
>           vcpuTCBPtr = Nothing
>         , vcpuVGIC = VGICInterface {
>                           vgicHCR = vgicHCREN
>                         , vgicVMCR = 0
>                         , vgicAPR = 0
>                         , vgicLR = vgicLR
>                         }
>         , vcpuRegs = funArray (const 0) // [(VCPURegSCTLR, sctlrDefault)
>                                            ,(VCPURegACTLR, actlrDefault)]
>         , vcpuVPPIMasked = funArray (const False)
>         , vcpuVTimer = VirtTimer 0
>         }

#endif

\subsection{Time}

Converting Time to and from a list of words.

> parseTimeArg :: Int -> [Word] -> Time
> parseTimeArg i args = fromIntegral (args !! (i+1)) `shiftL` 32 + fromIntegral (args !! i)

> wordsOfTime :: Time -> [Word]
> wordsOfTime t = fromIntegral t : [fromIntegral $ t `shiftR` 32]
