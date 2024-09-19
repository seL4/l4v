--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains operations on machine-specific object types.

-- TODO AARCH64: SMMU issues are pointed out in cases where a default match exists.

module SEL4.Object.ObjectType.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet
import SEL4.Machine.Hardware.AARCH64
import SEL4.Model
import SEL4.Model.StateData.AARCH64
import SEL4.API.Types
import SEL4.API.Failures
import SEL4.API.Invocation.AARCH64 as ArchInv
import SEL4.Object.Structures
import SEL4.Kernel.VSpace.AARCH64
import SEL4.Object.VCPU.AARCH64
import {-# SOURCE #-} SEL4.Object.TCB
import SEL4.Object.FPU.AARCH64

import Data.Bits
import Data.Word(Word16)
import Data.Array

-- The architecture-specific types and structures are qualified with the
-- "Arch.Types" and "Arch.Structures" prefixes, respectively. This is to avoid
-- namespace conflicts with the platform-independent modules.

import qualified SEL4.API.Types.AARCH64 as Arch.Types

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
deriveCap _ (c@VCPUCap {}) = return $ ArchObjectCap c
-- TODO AARCH64 SMMU: SID/CB control caps, SID/CB caps

isCapRevocable :: Capability -> Capability -> Bool
isCapRevocable newCap srcCap = False

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
        capPTType = VSRootPT_T,
        capPTMappedAddress = Just (asid, vptr),
        capPTBasePtr = pte }) True = do
    deleteASID asid pte
    return (NullCap, NullCap)

finaliseCap (PageTableCap {
        capPTType = NormalPT_T,
        capPTMappedAddress = Just (asid, vptr),
        capPTBasePtr = pte }) True = do
    unmapPageTable asid vptr pte
    return (NullCap, NullCap)

finaliseCap (FrameCap {
        capFMappedAddress = Just (asid, v),
        capFSize = s,
        capFBasePtr = ptr }) _ = do
    unmapPage s asid v ptr
    return (NullCap, NullCap)

finaliseCap (VCPUCap { capVCPUPtr = vcpu }) True = do
    vcpuFinalise vcpu
    return (NullCap, NullCap)

-- TODO AARCH64 SMMU: C also has cap_cb_cap, cap_sid_cap (but not SID/CB control caps)

finaliseCap _ _ = return (NullCap, NullCap)

{- Identifying Capabilities -}

sameRegionAs :: ArchCapability -> ArchCapability -> Bool
sameRegionAs (a@FrameCap {}) (b@FrameCap {}) =
    (botA <= botB) && (topA >= topB) && (botB <= topB)
    where
        botA = capFBasePtr a
        botB = capFBasePtr b
        topA = botA + mask (pageBitsForSize $ capFSize a)
        topB = botB + mask (pageBitsForSize $ capFSize b)
sameRegionAs (a@PageTableCap {}) (b@PageTableCap {}) =
    capPTBasePtr a == capPTBasePtr b && capPTType a == capPTType b
sameRegionAs ASIDControlCap ASIDControlCap = True
sameRegionAs (a@ASIDPoolCap {}) (b@ASIDPoolCap {}) =
    capASIDPool a == capASIDPool b
sameRegionAs (a@VCPUCap {}) (b@VCPUCap {}) = capVCPUPtr a == capVCPUPtr b
-- TODO AARCH64 SMMU: SID/CB caps and control caps (which work a bit strangely here)
sameRegionAs _ _ = False

isPhysicalCap :: ArchCapability -> Bool
isPhysicalCap ASIDControlCap = False
-- TODO AARCH64 SMMU: in C, SMMU caps default to False but this needs review
isPhysicalCap _ = True

sameObjectAs :: ArchCapability -> ArchCapability -> Bool
sameObjectAs (a@FrameCap { capFBasePtr = ptrA }) (b@FrameCap {}) =
    (ptrA == capFBasePtr b) && (capFSize a == capFSize b)
        && (ptrA <= ptrA + mask (pageBitsForSize $ capFSize a))
        && (capFIsDevice a == capFIsDevice b)
-- TODO AARCH64 SMMU: SID/CB caps and control caps (which work a bit strangely here)
sameObjectAs a b = sameRegionAs a b

{- Creating New Capabilities -}

-- Create an architecture-specific object.

placeNewDataObject :: PPtr () -> Int -> Bool -> Kernel ()
placeNewDataObject regionBase sz isDevice = if isDevice
    then placeNewObject regionBase UserDataDevice sz
    else placeNewObject regionBase UserData sz

updatePTType :: PPtr () -> PT_Type -> Kernel ()
updatePTType p pt_t = do
    ptTypes <- gets (gsPTTypes . ksArchState)
    let funupd = (\f x v y -> if y == x then v else f y)
    let ptTypes' = funupd ptTypes (fromPPtr p) (Just pt_t)
    modify (\ks -> ks { ksArchState = (ksArchState ks) { gsPTTypes = ptTypes' } })

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
                     (fromPPtr regionBase) (Just ARMSmallPage)})
            when (not isDevice) $ doMachineOp $
                cleanCacheRange_RAM (VPtr $ fromPPtr regionBase)
                    (VPtr $ fromPPtr regionBase + mask (pageBitsForSize ARMSmallPage))
                    (addrFromPPtr regionBase)
            return $ FrameCap (pointerCast regionBase)
                  VMReadWrite ARMSmallPage isDevice Nothing
        Arch.Types.LargePageObject -> do
            placeNewDataObject regionBase (ptTranslationBits NormalPT_T) isDevice
            modify (\ks -> ks { gsUserPages =
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMLargePage)})
            when (not isDevice) $ doMachineOp $
                cleanCacheRange_RAM (VPtr $ fromPPtr regionBase)
                    (VPtr $ fromPPtr regionBase + mask (pageBitsForSize ARMLargePage))
                    (addrFromPPtr regionBase)
            return $ FrameCap (pointerCast regionBase)
                  VMReadWrite ARMLargePage isDevice Nothing
        Arch.Types.HugePageObject -> do
            placeNewDataObject regionBase (2*ptTranslationBits NormalPT_T) isDevice
            modify (\ks -> ks { gsUserPages =
              funupd (gsUserPages ks)
                     (fromPPtr regionBase) (Just ARMHugePage)})
            when (not isDevice) $ doMachineOp $
                cleanCacheRange_RAM (VPtr $ fromPPtr regionBase)
                    (VPtr $ fromPPtr regionBase + mask (pageBitsForSize ARMHugePage))
                    (addrFromPPtr regionBase)
            return $ FrameCap (pointerCast regionBase)
                  VMReadWrite ARMHugePage isDevice Nothing
        Arch.Types.PageTableObject -> do
            let ptSize = ptBits NormalPT_T - objBits (makeObject :: PTE)
            placeNewObject regionBase (makeObject :: PTE) ptSize
            updatePTType regionBase NormalPT_T
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr regionBase)
                    (VPtr $ fromPPtr regionBase + mask (ptBits NormalPT_T))
                    (addrFromPPtr regionBase)
            return $ PageTableCap (pointerCast regionBase) NormalPT_T Nothing
        Arch.Types.VSpaceObject -> do
            let ptSize = ptBits VSRootPT_T - objBits (makeObject :: PTE)
            placeNewObject regionBase (makeObject :: PTE) ptSize
            updatePTType regionBase VSRootPT_T
            doMachineOp $
                cleanCacheRange_PoU (VPtr $ fromPPtr regionBase)
                    (VPtr $ fromPPtr regionBase + mask (ptBits VSRootPT_T))
                    (addrFromPPtr regionBase)
            return $ PageTableCap (pointerCast regionBase) VSRootPT_T Nothing
        Arch.Types.VCPUObject -> do
            placeNewObject regionBase (makeObject :: VCPU) 0
            return $ VCPUCap (PPtr $ fromPPtr regionBase)

{- Capability Invocation -}

decodeInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeInvocation label args capIndex slot cap extraCaps =
    case cap of
       VCPUCap {} -> decodeARMVCPUInvocation label args capIndex slot cap extraCaps
       -- TODO AARCH64 SMMU: SID/CB control caps, SID/CB caps
       _ -> decodeARMMMUInvocation label args capIndex slot cap extraCaps

performInvocation :: ArchInv.Invocation -> KernelP [Word]
performInvocation i =
    case i of
        ArchInv.InvokeVCPU iv -> withoutPreemption $ performARMVCPUInvocation iv
        -- TODO AARCH64 SMMU: SID/CB control invocations, SID/CB invocations
        _ -> performARMMMUInvocation i

{- Helper Functions -}

capUntypedPtr :: ArchCapability -> PPtr ()
capUntypedPtr (FrameCap { capFBasePtr = PPtr p }) = PPtr p
capUntypedPtr (PageTableCap { capPTBasePtr = PPtr p }) = PPtr p
capUntypedPtr ASIDControlCap = error "ASID control has no pointer"
capUntypedPtr (ASIDPoolCap { capASIDPool = PPtr p }) = PPtr p
capUntypedPtr (VCPUCap { capVCPUPtr = PPtr p }) = PPtr p

asidPoolBits :: Int
asidPoolBits = 12

capUntypedSize :: ArchCapability -> Word
capUntypedSize (FrameCap {capFSize = sz}) = bit $ pageBitsForSize sz
capUntypedSize (PageTableCap {capPTType = pt_t}) = bit (ptBits pt_t)
capUntypedSize (ASIDControlCap {}) = 0
capUntypedSize (ASIDPoolCap {}) = bit asidPoolBits
capUntypedSize (VCPUCap {}) = bit vcpuBits

-- Thread deletion requires associated FPU cleanup

prepareThreadDelete :: PPtr TCB -> Kernel ()
prepareThreadDelete thread = do
    fpuRelease thread
    tcbVCPU <- archThreadGet atcbVCPUPtr thread
    case tcbVCPU of
      Just ptr -> dissociateVCPUTCB ptr thread
      _ -> return ()
