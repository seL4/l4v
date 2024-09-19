%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains operations on machine-specific object types for x64.

> module SEL4.Object.ObjectType.X64 where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine.RegisterSet
> import SEL4.Machine.Hardware.X64
> import SEL4.Model
> import SEL4.Model.StateData.X64
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Invocation.X64 as ArchInv
> import SEL4.Object.Structures
> import SEL4.Kernel.VSpace.X64
> import {-# SOURCE #-} SEL4.Object.IOPort.X64
> import SEL4.Object.FPU.X64

> import Data.Bits
> import Data.Word(Word16)
> import Data.Array

\end{impdetails}

The x64-specific types and structures are qualified with the "Arch.Types" and "Arch.Structures" prefixes, respectively. This is to avoid namespace conflicts with the platform-independent modules.

> import qualified SEL4.API.Types.X64 as Arch.Types

\subsection{Copying and Mutating Capabilities}

> deriveCap :: PPtr CTE -> ArchCapability -> KernelF SyscallError Capability

It is not possible to copy a page table or page directory capability unless it has been mapped.

> deriveCap _ (c@PageTableCap { capPTMappedAddress = Just _ }) = return $ ArchObjectCap c
> deriveCap _ (PageTableCap { capPTMappedAddress = Nothing })
>     = throw IllegalOperation
> deriveCap _ (c@PageDirectoryCap { capPDMappedAddress = Just _ }) = return $ ArchObjectCap c
> deriveCap _ (PageDirectoryCap { capPDMappedAddress = Nothing })
>     = throw IllegalOperation
> deriveCap _ (c@PDPointerTableCap { capPDPTMappedAddress = Just _ }) = return $ ArchObjectCap c
> deriveCap _ (PDPointerTableCap { capPDPTMappedAddress = Nothing })
>     = throw IllegalOperation
> deriveCap _ (c@PML4Cap { capPML4MappedASID = Just _ }) = return $ ArchObjectCap c
> deriveCap _ (PML4Cap { capPML4MappedASID = Nothing })
>     = throw IllegalOperation

Page capabilities are copied without their mapping information, to allow them to be mapped in multiple locations.

> deriveCap _ (c@PageCap {}) = return $ ArchObjectCap $ c { capVPMappedAddress = Nothing, capVPMapType = VMNoMap }

ASID capabilities can be copied without modification, as can IOPort and IOSpace caps.

> deriveCap _ c@ASIDControlCap = return $ ArchObjectCap c
> deriveCap _ (c@ASIDPoolCap {}) = return $ ArchObjectCap c
> deriveCap _ (c@IOPortCap {}) = return $ ArchObjectCap c
> deriveCap _ IOPortControlCap = return NullCap
> -- deriveCap _ (c@IOSpaceCap {}) = return c

% IOPTs

> -- deriveCap _ (c@IOPageTableCap { capIOPTMappedAddress = Just _ }) = return c
> -- deriveCap _ (IOPageTableCap { capIOPTMappedAddress = Nothing })
> --    = throw IllegalOperation -}

> isIOPortControlCap' :: Capability -> Bool
> isIOPortControlCap' (ArchObjectCap IOPortControlCap) = True
> isIOPortControlCap' _ = False

> isCapRevocable :: Capability -> Capability -> Bool
> isCapRevocable newCap srcCap = case newCap of
>     ArchObjectCap (IOPortCap {}) -> isIOPortControlCap' srcCap
>     _ -> False

Whether the first capability is a parent of the second one. Can assume that
sameRegionAs is true for the two capabilities. If this function returns True,
the remaining cases of generic isMDBParentOf are still checked.

> isArchMDBParentOf :: Capability -> Capability -> Bool -> Bool
> isArchMDBParentOf _ _ _ = True

% X64 has two writable user data caps

> -- FIXME x64: io_space_capdata_get_domainID
>-- ioSpaceGetDomainID :: Word -> Word16
>-- ioSpaceGetDomainID _ = error "Not implemented"

>-- -- FIXME x64: io_space_capdata_get_PCIDevice
>-- ioSpaceGetPCIDevice :: Word -> Maybe IOASID
>-- ioSpaceGetPCIDevice _ = error "Not implemented"

>-- ioPortGetFirstPort :: Word -> Word16
>-- ioPortGetFirstPort capdata = fromIntegral (shiftR capdata 16)

>-- ioPortGetLastPort :: Word -> Word16
>-- ioPortGetLastPort capdata = fromIntegral capdata

> updateCapData :: Bool -> Word -> ArchCapability -> Capability
>-- updateCapData preserve newData (c@IOSpaceCap {}) =
>--     let
>--         pciDevice = ioSpaceGetPCIDevice newData;
>--         domID = ioSpaceGetDomainID newData;
>--         fstValidDom = firstValidIODomain;
>--         domIDBits = numIODomainIDBits
>--     in
>--     if (not preserve && capIOPCIDevice c == Nothing && domID >= fstValidDom
>--                     && domID /= 0 && domID <= mask domIDBits)
>--                then (ArchObjectCap (IOSpaceCap domID pciDevice))
>--                else NullCap -}
>-- updateCapData preserve newData (c@IOPortCap {}) =
>--     let
>--         firstPort = ioPortGetFirstPort newData;
>--         lastPort = ioPortGetLastPort newData;
>--         oldFirst = capIOPortFirstPort c;
>--         oldLast = capIOPortLastPort c
>--     in
>--     if (not preserve && firstPort <= lastPort
>--             && firstPort >= oldFirst && lastPort <= oldLast)
>--         then (ArchObjectCap (IOPortCap firstPort lastPort))
>--         else NullCap
> updateCapData _ _ c = ArchObjectCap c

CNodes have differing numbers of guard bits and rights bits

> cteRightsBits :: Int
> cteRightsBits = 0

> cteGuardBits :: Int
> cteGuardBits = 58

Page capabilities have read and write permission bits, which are used to restrict virtual memory accesses to their contents. Note that the ability to map objects into a page table or page directory is granted by possession of a capability to it; there is no specific permission bit restricting this ability.

> maskCapRights :: CapRights -> ArchCapability -> Capability
> maskCapRights r c@(PageCap {}) = ArchObjectCap $ c {
>     capVPRights = maskVMRights (capVPRights c) r }
> maskCapRights _ c = ArchObjectCap c

\subsection{Deleting Capabilities}

> setIOPortMask :: IOPort -> IOPort -> Bool -> Kernel ()
> setIOPortMask f l val = do
>     ports <- gets (x64KSAllocatedIOPorts . ksArchState)
>     ports' <- return $ ports//[(i,val) | i <- [f..l]]
>     modify (\s -> s {
>         ksArchState = (ksArchState s) { x64KSAllocatedIOPorts = ports' }})

> freeIOPortRange :: IOPort -> IOPort -> Kernel ()
> freeIOPortRange f l = setIOPortMask f l False

> postCapDeletion :: ArchCapability -> Kernel ()
> postCapDeletion c = case c of
>     IOPortCap f l -> freeIOPortRange f l
>     _ -> return ()

> finaliseCap :: ArchCapability -> Bool -> Kernel (Capability, Capability)

Deletion of a final capability to an ASID pool requires that the pool is removed from the global ASID table.

> finaliseCap (ASIDPoolCap { capASIDBase = b, capASIDPool = ptr }) True = do
>     deleteASIDPool b ptr
>     return (NullCap, NullCap)

Delete a PML4

> finaliseCap (PML4Cap {
>         capPML4MappedASID = Just a,
>         capPML4BasePtr = ptr }) True = do
>     deleteASID a ptr
>     return (NullCap, NullCap)

Delete a PDPT

> finaliseCap (PDPointerTableCap {
>         capPDPTMappedAddress = Just (a, v),
>         capPDPTBasePtr = ptr }) True = do
>     unmapPDPT a v ptr
>     return (NullCap, NullCap)


Deletion of a final capability to a page directory with an assigned ASID requires the ASID assignment to be removed, and the ASID flushed from the caches.

> finaliseCap (PageDirectoryCap {
>         capPDMappedAddress = Just (a, v),
>         capPDBasePtr = ptr }) True = do
>     unmapPageDirectory a v ptr
>     return (NullCap, NullCap)

Deletion of a final capability to a page table that has been mapped requires that the mapping be removed from the page directory, and the corresponding addresses flushed from the caches.

> finaliseCap (PageTableCap {
>         capPTMappedAddress = Just (a, v),
>         capPTBasePtr = ptr }) True = do
>     unmapPageTable a v ptr
>     return (NullCap, NullCap)

> --finaliseCap (IOSpaceCap {}) True = return (NullCap, NullCap) -- FIXME x64: not yet implemented in C

> finaliseCap (PageCap {
>         capVPMappedAddress = Just (a, v),
>         capVPSize = s,
>         capVPBasePtr = ptr }) _ = do
>     unmapPage s a v ptr
>     return (NullCap, NullCap)

> finaliseCap (IOPortCap f l) True = return (NullCap, (ArchObjectCap (IOPortCap f l)))

> finaliseCap _ _ = return (NullCap, NullCap)

%Note: limitations in Haskell translator caseconvs makes this horrible

>-- finaliseCap c b = case (c, b) of
>--     ((IOPageTableCap { capIOPTMappedAddress = Just (asid,ioaddr),
>--                                capIOPTLevel = level,
>--                              capIOPTBasePtr = baseptr  }), True) -> do
>--         deleteIOPageTable c
>--         unmapIOPageTable level asid ioaddr baseptr
>--         return NullCap
>--     ((PageCap { capVPMappedAddress = Just (asid, vaddr),
>--                          capVPSize = vpsz,
>--                       capVPMapType = VMIOSpaceMap,
>--                       capVPBasePtr = baseptr}), _) -> do
>--         unmapIOPage vpsz (fromIntegral asid) vaddr baseptr
>--         return NullCap
>--     ((PageCap { capVPMappedAddress = Just (a, v), capVPSize = s, capVPBasePtr = ptr }), _) -> do
>--         unmapPage s a v ptr
>--         return NullCap
>--     (_, _) -> return NullCap -}
>--

\subsection{Identifying Capabilities}

> isIRQControlCapDescendant :: ArchCapability -> Bool
> isIRQControlCapDescendant _ = False

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
> sameRegionAs (a@PDPointerTableCap {}) (b@PDPointerTableCap {}) =
>     capPDPTBasePtr a == capPDPTBasePtr b
> sameRegionAs (a@PML4Cap {}) (b@PML4Cap {}) =
>     capPML4BasePtr a == capPML4BasePtr b
> sameRegionAs ASIDControlCap ASIDControlCap = True
> sameRegionAs (a@ASIDPoolCap {}) (b@ASIDPoolCap {}) =
>     capASIDPool a == capASIDPool b
> sameRegionAs (a@IOPortCap {}) (b@IOPortCap {}) =
>     (fA == fB) && (lB == lA)
>     where
>         fA = capIOPortFirstPort a
>         fB = capIOPortFirstPort b
>         lA = capIOPortLastPort a
>         lB = capIOPortLastPort b
> sameRegionAs IOPortControlCap IOPortControlCap = True
> sameRegionAs IOPortControlCap (IOPortCap {}) = True
> --sameRegionAs (a@IOSpaceCap {}) (b@IOSpaceCap {}) =
> --    capIOPCIDevice a == capIOPCIDevice b
> --sameRegionAs (a@IOPageTableCap {}) (b@IOPageTableCap {}) =
> --    capIOPTBasePtr a == capIOPTBasePtr b -}
> sameRegionAs _ _ = False

> isPhysicalCap :: ArchCapability -> Bool
> isPhysicalCap ASIDControlCap = False
> isPhysicalCap (IOPortCap _ _) = False
> isPhysicalCap IOPortControlCap = False
> isPhysicalCap _ = True

> sameObjectAs :: ArchCapability -> ArchCapability -> Bool
> sameObjectAs (a@PageCap { capVPBasePtr = ptrA }) (b@PageCap {}) =
>     (ptrA == capVPBasePtr b) && (capVPSize a == capVPSize b)
>         && (ptrA <= ptrA + bit (pageBitsForSize $ capVPSize a) - 1)
>         && (capVPIsDevice a == capVPIsDevice b)
> sameObjectAs IOPortControlCap (IOPortCap {}) = False
> sameObjectAs a b = sameRegionAs a b

\subsection{Creating New Capabilities}

Create an architecture-specific object.

% FIXME: it is not clear wheather we can have large device page

> placeNewDataObject :: PPtr () -> Int -> Bool -> Kernel ()
> placeNewDataObject regionBase sz isDevice = if isDevice
>     then placeNewObject regionBase UserDataDevice sz
>     else placeNewObject regionBase UserData sz

> createObject :: ObjectType -> PPtr () -> Int -> Bool -> Kernel ArchCapability
> createObject t regionBase _ isDevice =
>     let funupd = (\f x v y -> if y == x then v else f y) in
>     let pointerCast = PPtr . fromPPtr
>     in case t of
>         Arch.Types.APIObjectType _ ->
>             fail "Arch.createObject got an API type"
>         Arch.Types.SmallPageObject -> do
>             placeNewDataObject regionBase 0 isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just X64SmallPage)})
>             return $ PageCap (pointerCast regionBase)
>                   VMReadWrite VMNoMap X64SmallPage isDevice Nothing
>         Arch.Types.LargePageObject -> do
>             placeNewDataObject regionBase ptTranslationBits isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just X64LargePage)})
>             return $ PageCap (pointerCast regionBase)
>                   VMReadWrite VMNoMap X64LargePage isDevice Nothing
>         Arch.Types.HugePageObject -> do
>             placeNewDataObject regionBase (ptTranslationBits + ptTranslationBits) isDevice
>             modify (\ks -> ks { gsUserPages =
>               funupd (gsUserPages ks)
>                      (fromPPtr regionBase) (Just X64HugePage)})
>             return $ PageCap (pointerCast regionBase)
>                   VMReadWrite VMNoMap X64HugePage isDevice Nothing
>         Arch.Types.PageTableObject -> do
>             let ptSize = ptBits - objBits (makeObject :: PTE)
>             placeNewObject regionBase (makeObject :: PTE) ptSize
>             return $ PageTableCap (pointerCast regionBase) Nothing
>         Arch.Types.PageDirectoryObject -> do
>             let pdSize = pdBits - objBits (makeObject :: PDE)
>             placeNewObject regionBase (makeObject :: PDE) pdSize
>             return $ PageDirectoryCap (pointerCast regionBase) Nothing
>         Arch.Types.PDPointerTableObject -> do
>             let pdptSize = pdptBits - objBits (makeObject :: PDPTE)
>             placeNewObject regionBase (makeObject :: PDPTE) pdptSize
>             return $ PDPointerTableCap (pointerCast regionBase) Nothing
>         Arch.Types.PML4Object -> do
>             let pml4Size = pml4Bits - objBits (makeObject :: PML4E)
>             placeNewObject regionBase (makeObject :: PML4E) pml4Size
>             copyGlobalMappings (pointerCast regionBase)
>             return $ PML4Cap (pointerCast regionBase) Nothing

\subsection{Capability Invocation}

> isIOCap :: ArchCapability -> Bool
> isIOCap c = case c of
>          (IOPortCap {}) -> True
>          IOPortControlCap -> True
> --         (IOSpaceCap {}) -> True
>          _ -> False

> decodeInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation
> decodeInvocation label args capIndex slot cap extraCaps =
>     if isIOCap cap
>      then decodeX64PortInvocation label args slot cap $ map fst extraCaps
>      else decodeX64MMUInvocation label args capIndex slot cap extraCaps

> performInvocation :: ArchInv.Invocation -> KernelP [Word]
> performInvocation (oper@(InvokeIOPort _)) = performX64PortInvocation oper
> performInvocation (oper@(InvokeIOPortControl _)) = performX64PortInvocation oper
> performInvocation oper = performX64MMUInvocation oper

\subsection{Helper Functions}

> capUntypedPtr :: ArchCapability -> PPtr ()
> capUntypedPtr (PageCap { capVPBasePtr = PPtr p }) = PPtr p
> capUntypedPtr (PageTableCap { capPTBasePtr = PPtr p }) = PPtr p
> capUntypedPtr (PageDirectoryCap { capPDBasePtr = PPtr p }) = PPtr p
> capUntypedPtr (PDPointerTableCap { capPDPTBasePtr = PPtr p}) = PPtr p
> capUntypedPtr (PML4Cap { capPML4BasePtr = PPtr p}) = PPtr p
> capUntypedPtr ASIDControlCap = error "ASID control has no pointer"
> capUntypedPtr (ASIDPoolCap { capASIDPool = PPtr p }) = PPtr p
> capUntypedPtr (IOPortCap {}) = error "IOPortCap has no pointer"
> capUntypedPtr IOPortControlCap = error "IOPortControlCaps have no pointer"
> --capUntypedPtr (IOSpaceCap {}) = error "IOSpaceCap has no pointer"
> --capUntypedPtr (IOPageTableCap { capIOPTBasePtr = PPtr p }) = PPtr p


> capUntypedSize :: ArchCapability -> Word
> capUntypedSize (PageCap {capVPSize = sz}) = 1 `shiftL` pageBitsForSize sz
> capUntypedSize (PageTableCap {}) = 1 `shiftL` 12
> capUntypedSize (PageDirectoryCap {}) = 1 `shiftL` 12
> capUntypedSize (PDPointerTableCap {}) = 1 `shiftL` 12
> capUntypedSize (PML4Cap {}) = 1 `shiftL` 12
> capUntypedSize (ASIDControlCap {}) = 0
> capUntypedSize (ASIDPoolCap {}) = 1 `shiftL` (asidLowBits + 3)
> capUntypedSize (IOPortCap {}) = 0
> capUntypedSize IOPortControlCap = 0
> --capUntypedSize (IOSpaceCap {}) = 0
> --capUntypedSize (IOPageTableCap {}) = 1 `shiftL` 12

Notify the FPU when deleting a thread, in case that thread is using the FPU

> prepareThreadDelete :: PPtr TCB -> Kernel ()
> prepareThreadDelete threadPtr = fpuRelease threadPtr

