--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains operations on machine-specific object types.

module SEL4.Object.ObjectType.RISCV64 where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet
import SEL4.Machine.Hardware.RISCV64
import SEL4.Model
import SEL4.Model.StateData.RISCV64
import SEL4.API.Types
import SEL4.API.Failures
import SEL4.API.Invocation.RISCV64 as ArchInv
import SEL4.Object.Structures
import SEL4.Kernel.VSpace.RISCV64

import Data.Bits
import Data.Word(Word16)
import Data.Array

-- The architecture-specific types and structures are qualified with the
-- "Arch.Types" and "Arch.Structures" prefixes, respectively. This is to avoid
-- namespace conflicts with the platform-independent modules.

import qualified SEL4.API.Types.RISCV64 as Arch.Types

{- Copying and Mutating Capabilities -}

deriveCap :: PPtr CTE -> ArchCapability -> KernelF SyscallError Capability
-- It is not possible to copy a page table or page directory capability unless
-- it has been mapped.
deriveCap _ (c@PageTableCap { capPTMappedAddress = Just _ }) = return $ ArchObjectCap c
deriveCap _ (PageTableCap { capPTMappedAddress = Nothing })
    = throw IllegalOperation
-- Page capabilities are copied without their mapping information, to allow
-- them to be mapped in multiple locations.
deriveCap _ (c@FrameCap {})
    = return $ ArchObjectCap $ c { capFMappedAddress = Nothing }
-- ASID capabilities can be copied without modification
deriveCap _ c@ASIDControlCap = return $ ArchObjectCap c
deriveCap _ (c@ASIDPoolCap {}) = return $ ArchObjectCap c

isCapRevocable :: Capability -> Capability -> Bool
isCapRevocable newCap srcCap = False

-- Whether the first capability is a parent of the second one. Can assume that
-- sameRegionAs is true for the two capabilities. If this function returns True,
-- the remaining cases of generic isMDBParentOf are still checked.
isArchMDBParentOf :: Capability -> Capability -> Bool -> Bool
isArchMDBParentOf _ _ _ = True

updateCapData :: Bool -> Word -> ArchCapability -> Capability
updateCapData _ _ c = ArchObjectCap c

-- these seem to refer to extraction of fields from seL4_CNode_CapData

cteRightsBits :: Int
cteRightsBits = 0

cteGuardBits :: Int
cteGuardBits = 58

-- Page capabilities have read and write permission bits, which are used to
-- restrict virtual memory accesses to their contents. Note that the ability to
-- map objects into a page table or page directory is granted by possession of
-- a capability to it; there is no specific permission bit restricting this
-- ability.

maskCapRights :: CapRights -> ArchCapability -> Capability
maskCapRights r c@(FrameCap {}) = ArchObjectCap $ c {
    capFVMRights = maskVMRights (capFVMRights c) r }
maskCapRights _ c = ArchObjectCap c

{- Deleting Capabilities -}

postCapDeletion :: ArchCapability -> Kernel ()
postCapDeletion c = return ()

finaliseCap :: ArchCapability -> Bool -> Kernel (Capability, Capability)

finaliseCap (ASIDPoolCap { capASIDBase = b, capASIDPool = ptr }) True = do
    deleteASIDPool b ptr
    return (NullCap, NullCap)

finaliseCap (PageTableCap {
        capPTMappedAddress = Just (asid, vptr),
        capPTBasePtr = pte }) True = do

    catchFailure
        (do
            vroot <- findVSpaceForASID asid
            if vroot == pte
                then withoutFailure $ deleteASID asid pte
                else throw InvalidRoot)
        (\_ -> unmapPageTable asid vptr pte)

    return (NullCap, NullCap)

finaliseCap (FrameCap {
        capFMappedAddress = Just (asid, v),
        capFSize = s,
        capFBasePtr = ptr }) _ = do
    unmapPage s asid v ptr
    return (NullCap, NullCap)

finaliseCap _ _ = return (NullCap, NullCap)

{- Identifying Capabilities -}

isIRQControlCapDescendant :: ArchCapability -> Bool
isIRQControlCapDescendant _ = False

sameRegionAs :: ArchCapability -> ArchCapability -> Bool
sameRegionAs (a@FrameCap {}) (b@FrameCap {}) =
    (botA <= botB) && (topA >= topB) && (botB <= topB)
    where
        botA = capFBasePtr a
        botB = capFBasePtr b
        topA = botA + mask (pageBitsForSize $ capFSize a)
        topB = botB + mask (pageBitsForSize $ capFSize b)
sameRegionAs (a@PageTableCap {}) (b@PageTableCap {}) =
    capPTBasePtr a == capPTBasePtr b
sameRegionAs ASIDControlCap ASIDControlCap = True
sameRegionAs (a@ASIDPoolCap {}) (b@ASIDPoolCap {}) =
    capASIDPool a == capASIDPool b
sameRegionAs _ _ = False

isPhysicalCap :: ArchCapability -> Bool
isPhysicalCap ASIDControlCap = False
isPhysicalCap _ = True

sameObjectAs :: ArchCapability -> ArchCapability -> Bool
sameObjectAs (a@FrameCap { capFBasePtr = ptrA }) (b@FrameCap {}) =
    (ptrA == capFBasePtr b) && (capFSize a == capFSize b)
        && (ptrA <= ptrA + mask (pageBitsForSize $ capFSize a))
        && (capFIsDevice a == capFIsDevice b)
sameObjectAs a b = sameRegionAs a b

{- Creating New Capabilities -}

-- Create an architecture-specific object.

placeNewDataObject :: PPtr () -> Int -> Bool -> Kernel ()
placeNewDataObject regionBase sz isDevice = if isDevice
    then placeNewObject regionBase UserDataDevice sz
    else placeNewObject regionBase UserData sz

createObject :: ObjectType -> PPtr () -> Int -> Bool -> Kernel ArchCapability
createObject t regionBase _ isDevice =
    let funupd = (\f x v y -> if y == x then v else f y) in
    let pointerCast = PPtr . fromPPtr
    in case t of
        Arch.Types.APIObjectType _ ->
            fail "Arch.createObject got an API type"
        Arch.Types.SmallPageObject -> do
            placeNewDataObject regionBase 0 isDevice
            modify (\ks -> ks { gsUserPages =
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just RISCVSmallPage)})
            return $ FrameCap (pointerCast regionBase)
                  VMReadWrite RISCVSmallPage isDevice Nothing
        Arch.Types.LargePageObject -> do
            placeNewDataObject regionBase ptTranslationBits isDevice
            modify (\ks -> ks { gsUserPages =
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just RISCVLargePage)})
            return $ FrameCap (pointerCast regionBase)
                  VMReadWrite RISCVLargePage isDevice Nothing
        Arch.Types.HugePageObject -> do
            placeNewDataObject regionBase (ptTranslationBits+ptTranslationBits) isDevice
            modify (\ks -> ks { gsUserPages =
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just RISCVHugePage)})
            return $ FrameCap (pointerCast regionBase)
                  VMReadWrite RISCVHugePage isDevice Nothing
        Arch.Types.PageTableObject -> do
            let ptSize = ptBits - objBits (makeObject :: PTE)
            placeNewObject regionBase (makeObject :: PTE) ptSize
            return $ PageTableCap (pointerCast regionBase) Nothing

{- Capability Invocation -}

-- The only Arch invocations on RISCV are MMU invocations

decodeInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeInvocation = decodeRISCVMMUInvocation

performInvocation :: ArchInv.Invocation -> KernelP [Word]
performInvocation = performRISCVMMUInvocation

{- Helper Functions -}

capUntypedPtr :: ArchCapability -> PPtr ()
capUntypedPtr (FrameCap { capFBasePtr = PPtr p }) = PPtr p
capUntypedPtr (PageTableCap { capPTBasePtr = PPtr p }) = PPtr p
capUntypedPtr ASIDControlCap = error "ASID control has no pointer"
capUntypedPtr (ASIDPoolCap { capASIDPool = PPtr p }) = PPtr p

asidPoolBits :: Int
asidPoolBits = 12

capUntypedSize :: ArchCapability -> Word
capUntypedSize (FrameCap {capFSize = sz}) = bit $ pageBitsForSize sz
capUntypedSize (PageTableCap {}) = bit ptBits
capUntypedSize (ASIDControlCap {}) = 0
capUntypedSize (ASIDPoolCap {}) = bit asidPoolBits

-- No arch-specific thread deletion operations needed on RISC-V.

prepareThreadDelete :: PPtr TCB -> Kernel ()
prepareThreadDelete _ = return ()

-- No arch-specific operations needed before changing the domain of a TCB on
-- RISC-V.

prepareSetDomain :: PPtr TCB -> Domain -> Kernel ()
prepareSetDomain t newDom = return ()
