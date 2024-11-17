%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains operations on machine-specific object types for the ARM.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.ObjectType.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine.RegisterSet
> import SEL4.Machine.Hardware.ARM
> import SEL4.Model
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Invocation.ARM as ArchInv
> import SEL4.Object.Structures
> import SEL4.Kernel.VSpace.ARM
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Object.VCPU.ARM
#endif
> import {-# SOURCE #-} SEL4.Object.TCB

> import Data.Bits
> import Data.WordLib

\end{impdetails}

The ARM-specific types and structures are qualified with the "Arch.Types" and "Arch.Structures" prefixes, respectively. This is to avoid namespace conflicts with the platform-independent modules.

> import qualified SEL4.API.Types.ARM as Arch.Types

\subsection{Copying and Mutating Capabilities}

> deriveCap :: PPtr CTE -> ArchCapability -> KernelF SyscallError Capability

It is not possible to copy a page table or page directory capability unless it has been mapped.

> deriveCap _ (c@PageTableCap { capPTMappedAddress = Just _ }) = return $ ArchObjectCap c
> deriveCap _ (PageTableCap { capPTMappedAddress = Nothing })
>     = throw IllegalOperation
> deriveCap _ (c@PageDirectoryCap { capPDMappedASID = Just _ }) = return $ ArchObjectCap c
> deriveCap _ (PageDirectoryCap { capPDMappedASID = Nothing })
>     = throw IllegalOperation

Page capabilities are copied without their mapping information, to allow them to be mapped in multiple locations.

> deriveCap _ (c@PageCap {}) = return $ ArchObjectCap $ c  { capVPMappedAddress = Nothing }

ASID capabilities can be copied without modification.

> deriveCap _ c@ASIDControlCap = return $ ArchObjectCap c
> deriveCap _ (c@ASIDPoolCap {}) = return $ ArchObjectCap c

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> deriveCap _ (c@VCPUCap {}) = return $ ArchObjectCap c
#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

#ifdef CONFIG_ARM_SMMU
> deriveCap _ (c@IOSpaceCap {}) = return $ ArchObjectCap c
> deriveCap _ (c@IOPageTableCap {}) = error "FIXME ARMHYP_SMMU"
#endif /* CONFIG_ARM_SMMU */

> isCapRevocable :: Capability -> Capability -> Bool
> isCapRevocable _ _ = False

None of the ARM-specific capabilities have a user writeable data word.

> updateCapData :: Bool -> Word -> ArchCapability -> Capability
> updateCapData _ _ cap = ArchObjectCap cap

CNodes have differing numbers of guard bits and rights bits

> cteRightsBits :: Int
> cteRightsBits = 3

> cteGuardBits :: Int
> cteGuardBits = 18

Page capabilities have read and write permission bits, which are used to restrict virtual memory accesses to their contents. Note that the ability to map objects into a page table or page directory is granted by possession of a capability to it; there is no specific permission bit restricting this ability.

> maskCapRights :: CapRights -> ArchCapability -> Capability
> maskCapRights r c@(PageCap {}) = ArchObjectCap $ c {
>     capVPRights = maskVMRights (capVPRights c) r }
> maskCapRights _ c = ArchObjectCap c

\subsection{Deleting Capabilities}

> postCapDeletion :: ArchCapability -> Kernel ()
> postCapDeletion _ = return ()

> finaliseCap :: ArchCapability -> Bool -> Kernel (Capability, Capability)

Deletion of a final capability to an ASID pool requires that the pool is removed from the global ASID table.

> finaliseCap (ASIDPoolCap { capASIDBase = b, capASIDPool = ptr }) True = do
>     deleteASIDPool b ptr
>     return (NullCap, NullCap)

Deletion of a final capability to a page directory with an assigned ASID requires the ASID assignment to be removed, and the ASID flushed from the caches.

> finaliseCap (PageDirectoryCap {
>         capPDMappedASID = Just a,
>         capPDBasePtr = ptr }) True = do
>     deleteASID a ptr
>     return (NullCap, NullCap)

Deletion of a final capability to a page table that has been mapped requires that the mapping be removed from the page directory, and the corresponding addresses flushed from the caches.

> finaliseCap (PageTableCap {
>         capPTMappedAddress = Just (a, v),
>         capPTBasePtr = ptr }) True = do
>     unmapPageTable a v ptr
>     return (NullCap, NullCap)

Deletion of any mapped frame capability requires the page table slot to be located and cleared, and the unmapped address to be flushed from the caches.

> finaliseCap (cap@PageCap { capVPMappedAddress = Just (a, v),
>                            capVPSize = s, capVPBasePtr = ptr }) _ =
#ifdef CONFIG_ARM_SMMU
>     if capVPisIOSpace cap
>       then error "FIXME ARMHYP_SMMU"
>       else
#endif
>            do
>               unmapPage s a v ptr
>               return (NullCap, NullCap)

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> finaliseCap (VCPUCap { capVCPUPtr = vcpu }) True = do
>     vcpuFinalise vcpu
>     return (NullCap, NullCap)
#endif

#ifdef CONFIG_ARM_SMMU
> finaliseCap (IOSpaceCap {}) _ = error "FIXME ARMHYP_SMMU"
> finaliseCap (IOPageTableCap {}) _ = error "FIXME ARMHYP_SMMU" -- IO page directory does not need to be finalised
#endif

All other capabilities need no finalisation action.

> finaliseCap _ _ = return (NullCap, NullCap)


\subsection{Identifying Capabilities}

> sameRegionAs :: ArchCapability -> ArchCapability -> Bool
> sameRegionAs (a@PageCap {}) (b@PageCap {}) =
>     (botA <= botB) && (topA >= topB) && (botB <= topB)
>     where
>         botA = capVPBasePtr a
>         botB = capVPBasePtr b
>         topA = botA + bit (pageBitsForSize $ capVPSize a) - 1
>         topB = botB + bit (pageBitsForSize $ capVPSize b) - 1
> sameRegionAs (a@PageTableCap {}) (b@PageTableCap {}) =
>     capPTBasePtr a == capPTBasePtr b
> sameRegionAs (a@PageDirectoryCap {}) (b@PageDirectoryCap {}) =
>     capPDBasePtr a == capPDBasePtr b
> sameRegionAs ASIDControlCap ASIDControlCap = True
> sameRegionAs (a@ASIDPoolCap {}) (b@ASIDPoolCap {}) =
>     capASIDPool a == capASIDPool b
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> sameRegionAs (a@VCPUCap {}) (b@VCPUCap {}) = capVCPUPtr a == capVCPUPtr b
#endif
#ifdef CONFIG_ARM_SMMU
> sameRegionAs (a@IOSpaceCap {}) (b@IOSpaceCap {}) =
>     capIOSpaceModuleID a == capIOSpaceModuleID b
> sameRegionAs (a@IOPageTableCap {}) (b@IOPageTableCap {}) =
>     capIOPTBasePtr a == capIOPTBasePtr b
#endif
> sameRegionAs _ _ = False

> isPhysicalCap :: ArchCapability -> Bool
> isPhysicalCap ASIDControlCap = False
> isPhysicalCap _ = True

> sameObjectAs :: ArchCapability -> ArchCapability -> Bool
> sameObjectAs (a@PageCap { capVPBasePtr = ptrA }) (b@PageCap {}) =
>     (ptrA == capVPBasePtr b) && (capVPSize a == capVPSize b)
>         && (ptrA <= ptrA + bit (pageBitsForSize $ capVPSize a) - 1)
>         && (capVPIsDevice a == capVPIsDevice b)
> sameObjectAs a b = sameRegionAs a b

\subsection{Creating New Capabilities}

Creates a page-sized object that consists of plain words observable to the user.

> placeNewDataObject :: PPtr () -> Int -> Bool -> Kernel ()
> placeNewDataObject regionBase sz isDevice = if isDevice
>     then placeNewObject regionBase UserDataDevice sz
>     else placeNewObject regionBase UserData sz

Create an architecture-specific object.

> createObject :: ObjectType -> PPtr () -> Int -> Bool -> Kernel ArchCapability
> createObject t regionBase _ isDevice =
>     let funupd = (\f x v y -> if y == x then v else f y) in
>     let pointerCast = PPtr . fromPPtr in
#ifndef CONFIG_ARM_SMMU
>     let mkPageCap = \sz -> PageCap isDevice (pointerCast regionBase) VMReadWrite sz Nothing
#else
>     let mkPageCap = \sz -> PageCap isDevice (pointerCast regionBase) VMReadWrite sz False Nothing
#endif
>     in case t of
>         Arch.Types.APIObjectType _ ->
>             fail "Arch.createObject got an API type"
>         Arch.Types.SmallPageObject -> do
>             placeNewDataObject regionBase 0 isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just ARMSmallPage)})
>             when (not isDevice) $ doMachineOp $
>                 cleanCacheRange_RAM (VPtr $ fromPPtr regionBase)
>                     (VPtr $ fromPPtr regionBase + mask (pageBitsForSize ARMSmallPage))
>                     (addrFromPPtr regionBase)
>             return $ mkPageCap ARMSmallPage
>         Arch.Types.LargePageObject -> do
>             placeNewDataObject regionBase 4 isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just ARMLargePage)})
>             when (not isDevice) $ doMachineOp $
>                 cleanCacheRange_RAM (VPtr $ fromPPtr regionBase)
>                     (VPtr $ fromPPtr regionBase + mask (pageBitsForSize ARMLargePage))
>                     (addrFromPPtr regionBase)
>             return $ mkPageCap ARMLargePage
>         Arch.Types.SectionObject -> do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>             placeNewDataObject regionBase 9 isDevice
#else
>             placeNewDataObject regionBase 8 isDevice
#endif
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just ARMSection)})
>             when (not isDevice) $ doMachineOp $
>                 cleanCacheRange_RAM (VPtr $ fromPPtr regionBase)
>                     (VPtr $ fromPPtr regionBase + mask (pageBitsForSize ARMSection))
>                     (addrFromPPtr regionBase)
>             return $ mkPageCap ARMSection
>         Arch.Types.SuperSectionObject -> do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>             placeNewDataObject regionBase 13 isDevice
#else
>             placeNewDataObject regionBase 12 isDevice
#endif
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just ARMSuperSection)})
>             when (not isDevice) $ doMachineOp $
>                 cleanCacheRange_RAM (VPtr $ fromPPtr regionBase)
>                     (VPtr $ fromPPtr regionBase + mask (pageBitsForSize ARMSuperSection))
>                     (addrFromPPtr regionBase)
>             return $ mkPageCap ARMSuperSection
>         Arch.Types.PageTableObject -> do
>             let ptSize = ptBits - objBits (makeObject :: PTE)
>             placeNewObject regionBase (makeObject :: PTE) ptSize
>             doMachineOp $
>                 cleanCacheRange_PoU (VPtr $ fromPPtr regionBase)
>                     (VPtr $ fromPPtr regionBase + mask ptBits)
>                     (addrFromPPtr regionBase)
>             return $ PageTableCap (pointerCast regionBase) Nothing
>         Arch.Types.PageDirectoryObject -> do
>             let pdSize = pdBits - objBits (makeObject :: PDE)
>             placeNewObject regionBase (makeObject :: PDE) pdSize
>             copyGlobalMappings (pointerCast regionBase)
>             doMachineOp $
>                 cleanCacheRange_PoU (VPtr $ fromPPtr regionBase)
>                       (VPtr $ fromPPtr regionBase + mask pdBits)
>                       (addrFromPPtr regionBase)
>             return $ PageDirectoryCap (pointerCast regionBase) Nothing
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>         Arch.Types.VCPUObject -> do
>             placeNewObject regionBase (makeObject :: VCPU) 0
>             return $ VCPUCap (PPtr $ fromPPtr regionBase)
#endif
#ifdef CONFIG_ARM_SMMU
>         Arch.Types.IOPageTableObject -> do
>             let ptSize = ioptBits -- see comment at ioptBits
>             error "FIXME ARMHYP_SMMU"
#endif

\subsection{Capability Invocation}

> decodeInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation
> decodeInvocation label args capIndex slot cap extraCaps =
>     case cap of
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>        VCPUCap {} -> decodeARMVCPUInvocation label args capIndex slot cap extraCaps
#endif
#ifdef CONFIG_ARM_SMMU
>        IOSpaceCap {} -> error "FIXME ARMHYP_SMMU"
>        IOPageTableCap {} -> error "FIXME ARMHYP_SMMU"
#endif
>        _ -> decodeARMMMUInvocation label args capIndex slot cap extraCaps

> performInvocation :: ArchInv.Invocation -> KernelP [Word]
> performInvocation i =
>     case i of
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>                  ArchInv.InvokeVCPU iv -> do
>                      withoutPreemption $ performARMVCPUInvocation iv
#endif
#ifdef CONFIG_ARM_SMMU
>                  ArchInv.InvokeIOSpace _ ->
>                      withoutPreemption $ error "FIXME ARMHYP_SMMU"
>                  ArchInv.InvokeIOPageTable _ ->
>                      withoutPreemption $ error "FIXME ARMHYP_SMMU"
#endif
>                  _ -> performARMMMUInvocation i

\subsection{Helper Functions}

> capUntypedPtr :: ArchCapability -> PPtr ()
> capUntypedPtr (PageCap { capVPBasePtr = PPtr p }) = PPtr p
> capUntypedPtr (PageTableCap { capPTBasePtr = PPtr p }) = PPtr p
> capUntypedPtr (PageDirectoryCap { capPDBasePtr = PPtr p }) = PPtr p
> capUntypedPtr ASIDControlCap = error "ASID control has no pointer"
> capUntypedPtr (ASIDPoolCap { capASIDPool = PPtr p }) = PPtr p
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> capUntypedPtr (VCPUCap { capVCPUPtr = PPtr p }) = PPtr p
#endif
#ifdef CONFIG_ARM_SMMU
> capUntypedPtr (IOSpaceCap {}) = error "FIXME ARMHYP_SMMU"
> capUntypedPtr (IOPageTableCap { capIOPTBasePtr = PPtr p }) = PPtr p
#endif

> capUntypedSize :: ArchCapability -> Word
> capUntypedSize (PageCap {capVPSize = sz}) = bit (pageBitsForSize sz)
> capUntypedSize (PageTableCap {}) = bit ptBits
> capUntypedSize (PageDirectoryCap {}) = bit pdBits
> capUntypedSize (ASIDControlCap {}) = bit (asidHighBits + 2)
> capUntypedSize (ASIDPoolCap {}) = bit (asidLowBits + 2)
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> capUntypedSize (VCPUCap {}) = bit vcpuBits
#endif
#ifdef CONFIG_ARM_SMMU
> capUntypedSize (IOSpaceCap {}) = 0 -- invalid, use C default FIXME ARMHYP
> capUntypedSize (IOPageTableCap {}) = bit ioptBits
#endif


A function called from finaliseCap in ObjectType.lhs to prepare a tcb for deletion:

> prepareThreadDelete :: PPtr TCB -> Kernel ()
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> prepareThreadDelete thread = do
>     tcbVCPU <- archThreadGet atcbVCPUPtr thread
>     case tcbVCPU of
>       Just ptr -> dissociateVCPUTCB ptr thread
>       _ -> return ()
#else
> prepareThreadDelete _ = return ()
#endif

