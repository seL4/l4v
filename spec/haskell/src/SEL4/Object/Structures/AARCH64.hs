--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains the physical memory model's representations of the
-- AArch64-specific data structures, as well as a type representing capabilities
-- to AArch64-specific objects.

{-# LANGUAGE EmptyDataDecls, GeneralizedNewtypeDeriving #-}

module SEL4.Object.Structures.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet
import SEL4.Machine.Hardware.AARCH64
import {-# SOURCE #-} SEL4.Object.Structures
import Data.Array
import Data.Helpers
import Data.Bits
import Data.Word(Word64, Word32, Word8)
import SEL4.Machine.RegisterSet.AARCH64 (VCPUReg(..))

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
        capPTType :: PT_Type,
        capPTMappedAddress :: Maybe (ASID, VPtr) }
    | VCPUCap {
        capVCPUPtr :: PPtr VCPU }
    | SGISignalCap {
        capSGIIRQ :: Word,
        capSGITargetMask :: Word }
    deriving (Eq, Show)

{- The range of allowable sizes for Untyped objects depends on addressable memory size. -}

minUntypedSizeBits :: Int
minUntypedSizeBits = 4

maxUntypedSizeBits :: Int
maxUntypedSizeBits = 47


{- Threads -}

data ArchTCB = ArchThread {
        atcbContext :: UserContext,
        atcbVCPUPtr :: Maybe (PPtr VCPU) }
    deriving Show

newArchTCB = ArchThread {
    atcbContext = newContext,
    atcbVCPUPtr = Nothing }

atcbContextSet :: UserContext -> ArchTCB -> ArchTCB
atcbContextSet uc atcb = atcb { atcbContext = uc }

atcbContextGet :: ArchTCB -> UserContext
atcbContextGet = atcbContext

data ArchTcbFlag = FpuDisabled

archTcbFlagToWord :: ArchTcbFlag -> Word
archTcbFlagToWord (FpuDisabled) = bit 0


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


{- VCPUs -}

type VIRQ = Word

data GICVCPUInterface = VGICInterface {
                           vgicHCR :: Word32,
                           vgicVMCR :: Word32,
                           vgicAPR :: Word32,
                           vgicLR :: Array Int VIRQ }
    deriving Show

data VirtTimer = VirtTimer { vtimerLastPCount :: Word64 }
    deriving Show

data VPPIEventIRQ = VPPIEventIRQ_VTimer
    deriving (Eq, Enum, Bounded, Ord, Ix, Show)

data VCPU = VCPUObj {
                vcpuTCBPtr :: Maybe (PPtr TCB)
                ,vcpuVGIC :: GICVCPUInterface
                ,vcpuRegs :: Array VCPUReg Word
                ,vcpuVPPIMasked :: Array VPPIEventIRQ Bool
                ,vcpuVTimer :: VirtTimer }
    deriving Show

vcpuSCTLR vcpu = vcpuRegs vcpu ! VCPURegSCTLR

-- makeObject specialised to VCPUs.

makeVCPUObject :: VCPU
makeVCPUObject =
    let vgicLR = funPartialArray (const (0 :: Word)) (0, gicVCPUMaxNumLR-1) in
    VCPUObj {
          vcpuTCBPtr = Nothing
        , vcpuVGIC = VGICInterface {
                          vgicHCR = vgicHCREN
                        , vgicVMCR = 0
                        , vgicAPR = 0
                        , vgicLR = vgicLR
                        }
        , vcpuRegs = funArray (const 0) // [(VCPURegSCTLR, sctlrEL1VM)]
        , vcpuVPPIMasked = funArray (const False)
        , vcpuVTimer = VirtTimer 0
        }


{- Kernel Objects -}

data ArchKernelObject
    = KOASIDPool ASIDPool
    | KOPTE PTE
    | KOVCPU VCPU
    deriving Show

archObjSize :: ArchKernelObject -> Int
archObjSize (KOASIDPool _) = pageBits
archObjSize (KOPTE _) = pteBits
archObjSize (KOVCPU _) = vcpuBits
