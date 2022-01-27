--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains the physical memory model's representations of the
-- RISC-V 64bit-specific data structures, as well as a type representing
-- capabilities to RISC-V-specific objects.

{-# LANGUAGE EmptyDataDecls, GeneralizedNewtypeDeriving #-}

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.

-- FIXME AARCH64: added ASID pool entry type and validated ASID high/low bits,
-- but no other checking yet.

module SEL4.Object.Structures.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet
import SEL4.Machine.Hardware.AARCH64
import Data.Array
import Data.Bits
import Data.Word(Word64, Word8)


{- Capabilities -}

data ArchCapability
    = ASIDControlCap
    | ASIDPoolCap {
        capASIDPool :: PPtr ASIDPool,
        capASIDBase :: ASID }
    | FrameCap {
        capFBasePtr :: PPtr Word,
        capFVMRights :: VMRights,
        capFSize :: VMPageSize,
        capFIsDevice :: Bool,
        capFMappedAddress :: Maybe (ASID, VPtr) }
    | PageTableCap {
        capPTBasePtr :: PPtr PTE,
        capPTMappedAddress :: Maybe (ASID, VPtr) }
    deriving (Eq, Show)

{- The range of allowable sizes for Untyped objects depends on addressable memory size. -}

minUntypedSizeBits :: Int
minUntypedSizeBits = 4

maxUntypedSizeBits :: Int
maxUntypedSizeBits = 38

{- Kernel Objects -}

data ArchKernelObject
    = KOASIDPool ASIDPool
    | KOPTE PTE
    deriving Show

archObjSize :: ArchKernelObject -> Int
archObjSize (KOASIDPool _) = pageBits
archObjSize (KOPTE _) = pteBits


{- Threads -}

data ArchTCB = ArchThread {
        atcbContext :: UserContext }
    deriving Show

newArchTCB = ArchThread {
    atcbContext = newContext }

atcbContextSet :: UserContext -> ArchTCB -> ArchTCB
atcbContextSet uc atcb = atcb { atcbContext = uc }

atcbContextGet :: ArchTCB -> UserContext
atcbContextGet = atcbContext


{- ASID Pools -}

{- Aarch64 HYP (EL-2) has 8-bit VM IDs, which are similar to hardware ASIDs. -}
newtype VMID = VMID Word8
    deriving (Eq, Ord, Show, Real, Integral, Enum, Num, Ix, Bounded)

{- For SMMU table roots there will be another constructor in this data type. -}
data ASIDPoolEntry = ASIDPoolVSpace {
        apVMID :: Maybe VMID,
        apVSpace :: PPtr PTE }
    deriving Show

newtype ASIDPool = ASIDPool (Array ASID (Maybe ASIDPoolEntry))
    deriving Show

newtype ASID = ASID { fromASID :: Word64 }
    deriving (Show, Eq, Ord, Enum, Real, Integral, Num, Bits, Ix, Bounded)

asidHighBits :: Int
asidHighBits = 7

asidLowBits :: Int
asidLowBits = 9

asidBits :: Int
asidBits = asidHighBits + asidLowBits

asidRange :: (ASID, ASID)
asidRange = (0, (1 `shiftL` asidBits) - 1)

asidHighBitsOf :: ASID -> ASID
asidHighBitsOf asid = (asid `shiftR` asidLowBits) .&. mask asidHighBits
