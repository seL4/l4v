%
% Copyright 2022, Proofcraft Pty Ltd
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the handling of the x64 hardware-defined page tables.

> module SEL4.Kernel.VSpace.X64 where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Failures.X64
> import SEL4.Machine.RegisterSet
> import SEL4.Machine.RegisterSet.X64 (Register(..))
> import SEL4.Machine.Hardware.X64
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Model.StateData.X64
>-- import SEL4.API.Invocation
> import SEL4.API.InvocationLabels
> import SEL4.API.InvocationLabels.X64
> import {-# SOURCE #-} SEL4.Object.CNode
> import {-# SOURCE #-} SEL4.Object.TCB
> import {-# SOURCE #-} SEL4.Kernel.Init
> import {-# SOURCE #-} SEL4.Kernel.CSpace

> import Data.Bits
> import Data.Maybe
> import Data.Array
> import Data.Word (Word32)

\end{impdetails}

The x64-specific invocations are imported with the "ArchInv" prefix. This is necessary to avoid namespace conflicts with the generic invocations.

> import SEL4.API.Invocation.X64 as ArchInv

\subsection{Constants}

All virtual addresses above "pptrUserTop" cannot be mapped by user-level tasks. With the exception of one page, at "globalsBase", they cannot be read; the globals page is mapped read-only.

> globalsBase :: VPtr
> globalsBase = VPtr 0xffffc000

The idle thread's code is at an arbitrary location in kernel memory. For convenience in the Haskell model, we place it in the globals frame, but there is no need for it to be in user-accessible memory.

> idleThreadStart :: VPtr
> idleThreadStart = globalsBase + VPtr 0x100

> --x86KSnumIOPTLevels = 4

\subsubsection{Creating a New Address Space}

When a new page directory is created, the kernel copies all of the global mappings from the kernel page directory into the new page directory.

> copyGlobalMappings :: PPtr PML4E -> Kernel ()
> copyGlobalMappings newPM = do
>     skimPM <- gets (x64KSSKIMPML4 . ksArchState)
>     let base = getPML4Index pptrBase
>     let pml4eBits = objBits (undefined :: PML4E) -- = 3, size of word
>     let pmSize = 1 `shiftL` ptTranslationBits -- 512 entries in table
>     forM_ [base .. pmSize - 1] $ \index -> do
>         let offset = PPtr index `shiftL` pml4eBits
>         pml4e <- getObject $ skimPM + offset
>         storePML4E (newPM + offset) pml4e

> createMappingEntries :: PAddr -> VPtr ->
>     VMPageSize -> VMRights -> VMAttributes -> PPtr PML4E ->
>     KernelF SyscallError (VMPageEntry, VMPageEntryPtr)
> createMappingEntries base vptr X64SmallPage vmRights attrib vspace = do
>     p <- lookupErrorOnFailure False $ lookupPTSlot vspace vptr
>     return $ (VMPTE $ SmallPagePTE {
>         pteFrame = base,
>         pteGlobal = False,
>         ptePAT = x64PAT attrib,
>         pteDirty = False,
>         pteAccessed = False,
>         pteCacheDisabled = x64CacheDisabled attrib,
>         pteWriteThrough = x64WriteThrough attrib,
>         pteExecuteDisable = False,
>         pteRights = vmRights }, VMPTEPtr p)
>
> createMappingEntries base vptr X64LargePage vmRights attrib vspace = do
>     p <- lookupErrorOnFailure False $ lookupPDSlot vspace vptr
>     return $ (VMPDE $ LargePagePDE {
>         pdeFrame = base,
>         pdeGlobal = False,
>         pdePAT = x64PAT attrib,
>         pdeDirty = False,
>         pdeAccessed = False,
>         pdeCacheDisabled = x64CacheDisabled attrib,
>         pdeWriteThrough = x64WriteThrough attrib,
>         pdeExecuteDisable = False,
>         pdeRights = vmRights }, VMPDEPtr p)
>
> createMappingEntries base vptr X64HugePage vmRights attrib vspace = do
>     p <- lookupErrorOnFailure False $ lookupPDPTSlot vspace vptr
>     return $ (VMPDPTE $ HugePagePDPTE {
>         pdpteFrame = base,
>         pdpteGlobal = False,
>         pdptePAT = False,
>         pdpteDirty = False,
>         pdpteAccessed = False,
>         pdpteCacheDisabled = x64CacheDisabled attrib,
>         pdpteWriteThrough = x64WriteThrough attrib,
>         pdpteExecuteDisable = False,
>         pdpteRights = vmRights }, VMPDPTEPtr p)

The following function is called before creating or modifying mappings in a page table or page directory, and is responsible for ensuring that the mapping is safe.

> ensureSafeMapping :: (VMPageEntry, VMPageEntryPtr) ->
>     KernelF SyscallError ()
> ensureSafeMapping (VMPTE InvalidPTE, _) = return ()
> ensureSafeMapping (VMPDE InvalidPDE, _) = return ()
> ensureSafeMapping (VMPDPTE InvalidPDPTE, _) = return ()
>
> ensureSafeMapping (VMPTE (SmallPagePTE {}), VMPTEPtr slot) = return ()
>
> ensureSafeMapping (VMPDE (LargePagePDE {}), VMPDEPtr slot) = do
>         pde <- withoutFailure $ getObject slot
>         case pde of
>             InvalidPDE -> return ()
>             LargePagePDE {} -> return ()
>             _ -> throw DeleteFirst
>
> ensureSafeMapping (VMPDPTE (HugePagePDPTE {}), VMPDPTEPtr slot) = do
>         pdpte <- withoutFailure $ getObject slot
>         case pdpte of
>             InvalidPDPTE -> return ()
>             HugePagePDPTE {} -> return ()
>             _ -> throw DeleteFirst
>
> ensureSafeMapping _ = fail "This should never happen"

\subsection{Lookups and Faults}

\subsubsection{IPC Buffer Accesses}

When the kernel tries to access a thread's IPC buffer, this function is called to determine whether the buffer exists and to find its physical address.

> lookupIPCBuffer :: Bool -> PPtr TCB -> Kernel (Maybe (PPtr Word))
> lookupIPCBuffer isReceiver thread = do
>     bufferPtr <- threadGet tcbIPCBuffer thread
>     bufferFrameSlot <- getThreadBufferSlot thread
>     bufferCap <- getSlotCap bufferFrameSlot
>     case bufferCap of
>         ArchObjectCap (PageCap {capVPIsDevice = False, capVPBasePtr = baseptr, capVPRights = rights, capVPSize = sz}) -> do
>             let pBits = pageBitsForSize sz
>             if (rights == VMReadWrite || not isReceiver && rights == VMReadOnly)
>               then do
>                  let ptr = baseptr + PPtr (fromVPtr bufferPtr .&. mask pBits)
>                  assert (ptr /= 0)
>                             "IPC buffer pointer must be non-null"
>                  return $ Just ptr
>               else return Nothing
>         _ -> return Nothing

\subsubsection{ASID Lookups}

Locating the page directory for a given ASID is necessary when updating or deleting a mapping given its ASID and virtual address.

> findVSpaceForASID :: ASID -> KernelF LookupFailure (PPtr PML4E)
> findVSpaceForASID asid = do
>     assert (asid > 0) "ASID 0 is used for objects that are not mapped"
>     assert (asid <= snd asidRange) "ASID out of range"
>     asidTable <- withoutFailure $ gets (x64KSASIDTable . ksArchState)
>     let poolPtr = asidTable!(asidHighBitsOf asid)
>     ASIDPool pool <- case poolPtr of
>         Just ptr -> withoutFailure $ getObject ptr
>         Nothing -> throw InvalidRoot
>     let pm = pool!(asidLowBitsOf asid)
>     case pm of
>         Just ptr -> do
>             assert (ptr /= 0) "findVSpaceForASID: found null PD"
>             withoutFailure $ checkPML4At ptr
>             return ptr
>         Nothing -> throw InvalidRoot

> -- FIXME x64: these are all now unused.

> checkPML4At :: PPtr PML4E -> Kernel ()
> checkPML4At _ = return ()

> checkPDPTAt :: PPtr PDPTE -> Kernel ()
> checkPDPTAt _ = return ()

> checkPDAt :: PPtr PDE -> Kernel ()
> checkPDAt _ = return ()

> checkPTAt :: PPtr PTE -> Kernel ()
> checkPTAt _ = return ()

\subsubsection{Locating Page Table and Page Directory Slots}

The "lookupPTSlot" function locates the page table slot that maps a given virtual address, and returns a pointer to the slot. It will throw a lookup failure if the required page directory slot does not point to a page table.

> lookupPTSlot :: PPtr PML4E -> VPtr -> KernelF LookupFailure (PPtr PTE)
> lookupPTSlot pm vptr = do
>     pdSlot <- lookupPDSlot pm vptr
>     pde <- withoutFailure $ getObject pdSlot
>     case pde of
>         PageTablePDE {} -> do
>             let pt = ptrFromPAddr $ pdeTable pde
>             withoutFailure $ lookupPTSlotFromPT pt vptr
>         _ -> throw $ MissingCapability pdShiftBits

> lookupPTSlotFromPT :: PPtr PTE -> VPtr -> Kernel (PPtr PTE)
> lookupPTSlotFromPT pt vptr = do
>     let ptIndex = getPTIndex vptr
>     let ptSlot = pt + (PPtr $ ptIndex `shiftL` 3)
>     checkPTAt pt
>     return ptSlot

> lookupPDSlot :: PPtr PML4E -> VPtr -> KernelF LookupFailure (PPtr PDE)
> lookupPDSlot pm vptr = do
>     pdptSlot <- lookupPDPTSlot pm vptr
>     pdpte <- withoutFailure $ getObject pdptSlot
>     case pdpte of
>         PageDirectoryPDPTE {} -> do
>             let pd = ptrFromPAddr $ pdpteTable pdpte
>             withoutFailure $ lookupPDSlotFromPD pd vptr
>         _ -> throw $ MissingCapability pdptShiftBits

> lookupPDSlotFromPD :: PPtr PDE -> VPtr -> Kernel (PPtr PDE)
> lookupPDSlotFromPD pt vptr = do
>     let ptIndex = getPDIndex vptr
>     let ptSlot = pt + (PPtr $ ptIndex `shiftL` 3)
>     checkPDAt pt
>     return ptSlot

> lookupPDPTSlot :: PPtr PML4E -> VPtr -> KernelF LookupFailure (PPtr PDPTE)
> lookupPDPTSlot pm vptr = do
>     let pml4Slot = lookupPML4Slot pm vptr
>     pml4e <- withoutFailure $ getObject pml4Slot
>     case pml4e of
>         PDPointerTablePML4E {} -> do
>             let pdpt = ptrFromPAddr $ pml4eTable pml4e
>             withoutFailure $ lookupPDPTSlotFromPDPT pdpt vptr
>         _ -> throw $ MissingCapability pml4ShiftBits

> lookupPDPTSlotFromPDPT :: PPtr PDPTE -> VPtr -> Kernel (PPtr PDPTE)
> lookupPDPTSlotFromPDPT pt vptr = do
>     let ptIndex = getPDPTIndex vptr
>     let ptSlot = pt + (PPtr $ ptIndex `shiftL` 3)
>     checkPDPTAt pt
>     return ptSlot


Similarly, "lookupPDSlot" locates a slot in the top-level page directory. However, it does not access the kernel state and never throws a fault, so it is not in the kernel monad.

> lookupPML4Slot :: PPtr PML4E -> VPtr -> PPtr PML4E
> lookupPML4Slot pm vptr =
>     let pmIndex = getPML4Index vptr
>     in pm + (PPtr $ pmIndex `shiftL` 3)

\subsubsection{Handling Faults}

If the kernel receives a VM fault from the CPU, it must determine the address and cause of the fault and then throw it to the user-level fault handler. The C datastructure to sture the cause of the fault has only 12 bits space, hence the mask. Only the lower bits are significant anyway.

> handleVMFault :: PPtr TCB -> VMFaultType -> KernelF Fault ()
> handleVMFault thread f = do
>     addr <- withoutFailure $ doMachineOp getFaultAddress
>     fault <- withoutFailure $ asUser thread $ getRegister (Register ErrorRegister)
>     case f of
>         X64DataFault -> throw $ ArchFault $ VMFault addr [0, fault .&. mask 5] -- FSR is 5 bits in x64
>         X64InstructionFault -> throw $ ArchFault $ VMFault addr [1, fault .&. mask 5]

\subsection{Unmapping and Deletion}

When a capability backing a virtual memory mapping is deleted, or when an explicit request is made to remove a mapping, the kernel must locate the corresponding entries in the page table or ASID table and remove them. It is also necessary to flush the removed mappings from the hardware caches.

\subsubsection{Deleting an ASID Pool}

> deleteASIDPool :: ASID -> PPtr ASIDPool -> Kernel ()
> deleteASIDPool base ptr = do
>     assert (asidLowBitsOf base == 0)
>         "ASID pool's base must be aligned"
>     asidTable <- gets (x64KSASIDTable . ksArchState)
>     when (asidTable!(asidHighBitsOf base) == Just ptr) $ do
>         ASIDPool pool <- getObject ptr
>         forM [0 .. (bit asidLowBits) - 1] $ \offset -> do
>             when (isJust $ pool ! offset) $ hwASIDInvalidate (base + offset) $ fromJust $ pool ! offset
>         let asidTable' = asidTable//[(asidHighBitsOf base, Nothing)]
>         modify (\s -> s {
>             ksArchState = (ksArchState s) { x64KSASIDTable = asidTable' }})
>         tcb <- getCurThread
>         setVMRoot tcb

\subsubsection{Deleting an Address Space}

> deleteASID :: ASID -> PPtr PML4E -> Kernel ()
> deleteASID asid pm = do
>     asidTable <- gets (x64KSASIDTable . ksArchState)
>     case asidTable!(asidHighBitsOf asid) of
>         Nothing -> return ()
>         Just poolPtr -> do
>             ASIDPool pool <- getObject poolPtr
>             when (pool!(asidLowBitsOf asid) == Just pm) $ do
>                 hwASIDInvalidate asid pm
>                 let pool' = pool//[(asidLowBitsOf asid, Nothing)]
>                 setObject poolPtr $ ASIDPool pool'
>                 tcb <- getCurThread
>                 setVMRoot tcb

\subsubsection{Deleting a PDPT}

> unmapPDPT :: ASID -> VPtr -> PPtr PDPTE -> Kernel ()
> unmapPDPT asid vaddr pdpt = ignoreFailure $ do
>     vspace <- findVSpaceForASID asid
>     let pmSlot = lookupPML4Slot vspace vaddr
>     pml4e <- withoutFailure $ getObject pmSlot
>     case pml4e of
>         PDPointerTablePML4E { pml4eTable = pt' } ->
>             if pt' == addrFromPPtr pdpt then return () else throw InvalidRoot
>         _ -> throw InvalidRoot
>     withoutFailure $ do
>         flushPDPT (fromPPtr vspace) asid
>         storePML4E pmSlot InvalidPML4E

\subsubsection{Deleting a Page Directory}

> unmapPageDirectory :: ASID -> VPtr -> PPtr PDE -> Kernel ()
> unmapPageDirectory asid vaddr pd = ignoreFailure $ do
>     vspace <- findVSpaceForASID asid
>     pdptSlot <- lookupPDPTSlot vspace vaddr
>     pdpte <- withoutFailure $ getObject pdptSlot
>     case pdpte of
>         PageDirectoryPDPTE { pdpteTable = pd' } ->
>             if pd' == addrFromPPtr pd then return () else throw InvalidRoot
>         _ -> throw InvalidRoot
>     withoutFailure $ do
>         flushPD (fromPPtr vspace) asid
>         storePDPTE pdptSlot InvalidPDPTE
>         invalidatePageStructureCacheASID (addrFromPPtr vspace) asid

\subsubsection{Deleting a Page Table}

> unmapPageTable :: ASID -> VPtr -> PPtr PTE -> Kernel ()
> unmapPageTable asid vaddr pt = ignoreFailure $ do
>     vspace <- findVSpaceForASID asid
>     pdSlot <- lookupPDSlot vspace vaddr
>     pde <- withoutFailure $ getObject pdSlot
>     case pde of
>         PageTablePDE { pdeTable = pt' } ->
>             if pt' == addrFromPPtr pt then return () else throw InvalidRoot
>         _ -> throw InvalidRoot -- FIXME x64: dummy throw
>     withoutFailure $ do
>         flushTable vspace vaddr pt asid
>         storePDE pdSlot InvalidPDE
>         invalidatePageStructureCacheASID (addrFromPPtr vspace) asid


\subsubsection{Unmapping a Frame}

> unmapPage :: VMPageSize -> ASID -> VPtr -> PPtr Word -> Kernel ()
> unmapPage size asid vptr ptr = ignoreFailure $ do
>     vspace <- findVSpaceForASID asid
>     case size of
>         X64SmallPage -> do
>             p <- lookupPTSlot vspace vptr
>             pte <- withoutFailure $ getObject p
>             checkMappingPPtr ptr (VMPTE pte)
>             withoutFailure $ storePTE p InvalidPTE
>         X64LargePage -> do
>             p <- lookupPDSlot vspace vptr
>             pde <- withoutFailure $ getObject p
>             checkMappingPPtr ptr (VMPDE pde)
>             withoutFailure $ storePDE p InvalidPDE
>         X64HugePage -> do
>             p <- lookupPDPTSlot vspace vptr
>             pdpte <- withoutFailure $ getObject p
>             checkMappingPPtr ptr (VMPDPTE pdpte)
>             withoutFailure $ storePDPTE p InvalidPDPTE
>     withoutFailure $ doMachineOp $ invalidateTranslationSingleASID vptr $ fromASID asid

This helper function checks that the mapping installed at a given PT or PD slot points at the given physical address. If that is not the case, the mapping being unmapped has already been displaced, and the unmap need not be performed.

> checkMappingPPtr :: PPtr Word -> VMPageEntry -> KernelF LookupFailure ()
> checkMappingPPtr pptr (VMPTE pte) =
>     case pte of
>         SmallPagePTE { pteFrame = base } ->
>             unless (base == addrFromPPtr pptr) $ throw InvalidRoot
>         _ -> throw InvalidRoot
> checkMappingPPtr pptr (VMPDE pde) =
>     case pde of
>         LargePagePDE { pdeFrame = base } ->
>             unless (base == addrFromPPtr pptr) $ throw InvalidRoot
>         _ -> throw InvalidRoot
> checkMappingPPtr pptr (VMPDPTE pdpte) =
>     case pdpte of
>         HugePagePDPTE { pdpteFrame = base } ->
>             unless (base == addrFromPPtr pptr) $ throw InvalidRoot
>         _ -> throw InvalidRoot

\subsection{Address Space Switching}

> getCurrentUserCR3 :: Kernel CR3
> getCurrentUserCR3 = gets (x64KSCurrentUserCR3 . ksArchState)

> setCurrentUserCR3 :: CR3 -> Kernel ()
> setCurrentUserCR3 cr3 =
>     modify (\s -> s { ksArchState = (ksArchState s) { x64KSCurrentUserCR3 = cr3 }})

> invalidatePageStructureCacheASID :: PAddr -> ASID -> Kernel ()
> invalidatePageStructureCacheASID p a = doMachineOp $ invalidateLocalPageStructureCacheASID p (fromASID a)

> setCurrentUserVSpaceRoot :: PAddr -> ASID -> Kernel ()
> setCurrentUserVSpaceRoot vspace asid = setCurrentUserCR3 $ makeCR3 vspace asid

> setVMRoot :: PPtr TCB -> Kernel ()
> setVMRoot tcb = do
>     threadRootSlot <- getThreadVSpaceRoot tcb
>     threadRoot <- getSlotCap threadRootSlot
>     catchFailure
>         (case threadRoot of
>             ArchObjectCap (PML4Cap {
>                     capPML4MappedASID = Just asid,
>                     capPML4BasePtr = pml4 }) -> do
>                 pml4' <- findVSpaceForASID asid
>                 when (pml4 /= pml4') $ throw InvalidRoot
>                 curCR3 <- withoutFailure $ getCurrentUserCR3
>                 when (curCR3 /= makeCR3 (addrFromPPtr pml4) asid) $
>                         withoutFailure $ setCurrentUserCR3 $ makeCR3 (addrFromPPtr pml4) asid
>             _ -> throw InvalidRoot)
>         (\_ -> do
>             skimPML4 <- gets (x64KSSKIMPML4 . ksArchState)
>             setCurrentUserVSpaceRoot (addrFromKPPtr skimPML4) 0)

\subsection{Helper Functions}


> isValidVTableRoot :: Capability -> Bool
> isValidVTableRoot
>     (ArchObjectCap (PML4Cap { capPML4MappedASID = Just _ })) = True
> isValidVTableRoot _ = False

The location of an IPC buffer is computed using the relevant bits of a VPtr as an offset within a frame.
The IPC buffer frame must be a frame capability, and the buffer must be aligned.

Note that implementations with separate high and low memory regions may also wish to limit valid IPC buffer frames to low memory, so the kernel can access them without extra mappings. This function may also be used to enforce cache colouring restrictions.

> checkValidIPCBuffer :: VPtr -> Capability -> KernelF SyscallError ()
> checkValidIPCBuffer vptr (ArchObjectCap (PageCap {capVPIsDevice = False})) = do
>     when (vptr .&. mask 10 /= 0) $ throw AlignmentError
>     return ()
> checkValidIPCBuffer _ _ = throw IllegalOperation

> maskVMRights :: VMRights -> CapRights -> VMRights
> maskVMRights r m = case (r, capAllowRead m, capAllowWrite m) of
>     (VMReadOnly, True, _) -> VMReadOnly
>     (VMReadWrite, True, False) -> VMReadOnly
>     (VMReadWrite, True, True) -> VMReadWrite
>     _ -> VMKernelOnly

\subsection{Flushing}

%FIXME x64: needs review

> flushAll :: Word -> ASID -> Kernel ()
> flushAll vspace asid  = doMachineOp $ invalidateASID vspace (fromASID asid)

> flushPDPT  :: Word -> ASID -> Kernel ()
> flushPDPT p a = flushAll p a

> flushPD :: Word -> ASID -> Kernel ()
> flushPD p a = flushAll p a


%FIXME x64: needs review

> flushTable :: PPtr PML4E -> VPtr -> PPtr PTE -> ASID -> Kernel ()
> flushTable _ vptr pt asid = do
>     assert (vptr .&. mask (ptTranslationBits + pageBits) == 0)
>         "vptr must be 2MB aligned"
>     let pteBits = objBits (undefined :: PTE)
>     let ptSize = 1 `shiftL` ptTranslationBits
>     forM_ [0 .. ptSize - 1] $ \index -> do
>         let offset = PPtr index `shiftL` pteBits
>         pte <- getObject $ pt + offset
>         case pte of
>             InvalidPTE -> return ()
>             _ -> let index' = index `shiftL` pageBits
>                  in doMachineOp $ invalidateTranslationSingleASID (VPtr $ (fromVPtr vptr) + index') $ fromASID asid

\subsection{Managing ASID Map}

> hwASIDInvalidate :: ASID -> PPtr PML4E -> Kernel ()
> hwASIDInvalidate asid vspace =
>     doMachineOp $ invalidateASID (fromPPtr vspace) (fromASID asid)

\subsection{Decoding x64 Invocations}

> attribsFromWord :: Word -> VMAttributes
> attribsFromWord w = VMAttributes {
>     x64WriteThrough = w `testBit` 0,
>     x64PAT = w `testBit` 2,
>     x64CacheDisabled = w `testBit` 1 }

> pageBase :: VPtr -> VMPageSize -> VPtr
> pageBase vaddr size = vaddr .&. (complement $ mask (pageBitsForSize size))

> userVTop :: Word
> userVTop = 0x00007fffffffffff

> decodeX64FrameInvocation :: Word -> [Word] -> PPtr CTE ->
>                    ArchCapability -> [(Capability, PPtr CTE)] ->
>                    KernelF SyscallError ArchInv.Invocation
> decodeX64FrameInvocation label args cte (cap@PageCap {}) extraCaps =
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel X64PageMap, vaddr:rightsMask:attr:_, (vspaceCap,_):_) -> do
>             (vspace,asid) <- case vspaceCap of
>                 ArchObjectCap (PML4Cap {
>                         capPML4MappedASID = Just asid,
>                         capPML4BasePtr = vspace })
>                     -> return (vspace, asid)
>                 _ -> throw $ InvalidCapability 1
>             case capVPMappedAddress cap of
>                 Just (asid', vaddr') -> do
>                     when (asid' /= asid) $ throw $ InvalidCapability 1
>                     when (capVPMapType cap /= VMVSpaceMap) $ throw IllegalOperation
>                     when (vaddr' /= VPtr vaddr) $ throw $ InvalidArgument 0
>                 Nothing -> do
>                     let vtop = vaddr + bit (pageBitsForSize $ capVPSize cap)
>                     when (VPtr vaddr > VPtr userVTop || VPtr vtop > VPtr userVTop) $
>                         throw $ InvalidArgument 0
>             vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
>             when (vspaceCheck /= vspace) $ throw $ InvalidCapability 1
>             let vmRights = maskVMRights (capVPRights cap) $
>                     rightsFromWord rightsMask
>             checkVPAlignment (capVPSize cap) (VPtr vaddr)
>             entries <- createMappingEntries (addrFromPPtr $ capVPBasePtr cap)
>                 (VPtr vaddr) (capVPSize cap) vmRights
>                 (attribsFromWord attr) vspace
>             ensureSafeMapping entries
>             return $ InvokePage $ PageMap {
>                 pageMapCap = ArchObjectCap $ cap { capVPMapType = VMVSpaceMap, capVPMappedAddress = Just (asid, VPtr vaddr) },
>                 pageMapCTSlot = cte,
>                 pageMapEntries = entries,
>                 pageMapVSpace = vspace }
>         (ArchInvocationLabel X64PageMap, _, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64PageUnmap, _, _) -> -- case capVPMapType cap of
>--             VMIOSpaceMap -> decodeX64IOFrameInvocation label args cte cap extraCaps
>--             _ ->
>               return $ InvokePage $ PageUnmap {
>                 pageUnmapCap = cap,
>                 pageUnmapCapSlot = cte }
>--         (ArchInvocationLabel X64PageMapIO, _, _) -> decodeX64IOFrameInvocation label args cte cap extraCaps
>         (ArchInvocationLabel X64PageGetAddress, _, _) -> return $ InvokePage $ PageGetAddr (capVPBasePtr cap)
>         _ -> throw IllegalOperation
> decodeX64FrameInvocation _ _ _ _ _ = fail "Unreachable"

>--decodeX64IOPTInvocation :: Word -> [Word] -> PPtr CTE -> ArchCapability ->
>--                   [(Capability, PPtr CTE)] ->
>--                   KernelF SyscallError ArchInv.Invocation
>--decodeX64IOPTInvocation label args cptr cap@(IOPageTableCap {}) extraCaps =
>--    case (invocationType label, args, extraCaps) of
>--        (ArchInvocationLabel X64IOPageTableMap, ioaddr:_, (iospaceCap,_):_) -> do
>--            when (isJust $ capIOPTMappedAddress cap ) $ throw $ InvalidCapability 0
>--            when (not (capVPSize cap == X64SmallPage)) $ throw $ InvalidCapability 0

>--            (deviceid,domainid) <- case iospaceCap of
>--                ArchObjectCap (IOSpaceCap {
>--                        capIODomainID = domainid,
>--                        capIOPCIDevice = Just deviceid })
>--                    -> return (deviceid, domainid)
>--                _ -> throw $ InvalidCapability 0


>--            paddr <- return $ addrFromPPtr $ capIOPTBasePtr cap
>--            pciRequestId <- withoutFailure $ pciRequestIDFromCap iospaceCap
>--            cteslot <-  withoutFailure $ lookupIOContextSlot pciRequestId
>--            cte  <- withoutFailure $ getObject cteslot
>--            case cte of
>--                VTDCTE did rmrr aw slptr tt present ->
>--                    if present then do
>--                        let vtdcte = VTDCTE { domainId = domainid,
>--                            reservedMemReg = False,
>--                            addressWidth = x86KSnumIOPTLevels - 2,
>--                            nxtLevelPtr = paddr,
>--                            translationType = NotTranslatedRequest,
>--                            ctePresent = True }
>--                            cap' =  cap { capIOPTLevel = 0,
>--                                      capIOPTMappedAddress = Just (deviceid, VPtr ioaddr)}
>--                        (return $ InvokeIOPageTable $ IOPageTableMapContext cap' cptr vtdcte cteslot)
>--                    else do
>--                        let vtdpte = ptrFromPAddr slptr
>--                        (slot, level) <- lookupErrorOnFailure False $ lookupIOPTSlot vtdpte ioaddr
>--                        level <- return $ x86KSnumIOPTLevels - level
>--                        pte <- withoutFailure $ getObject slot
>--                        case pte of
>--                            InvalidIOPTE -> do
>--                                let vtdpte = VTDPTE {
>--                                          framePtr = paddr,
>--                                          rw = VMReadWrite }
>--                                    cap' =  cap { capVPMapType = VMIOSpaceMap,
>--                                          capIOPTLevel = level
>--                                          capVMMappedAddress = Just (deviceid, VPtr ioaddr)}
>--                                (return $ InvokeIOPageTable $ IOPageTableMap cap' cptr vtdpte slot)
>--                            _ -> throw $ InvalidCapability 0
>--                _ -> throw $ InvalidCapability 0
>--        (ArchInvocationLabel X64IOPageTableMap, _, _) -> throw TruncatedMessage
>--        (ArchInvocationLabel X64IOPageTableUnmap, _, _) ->
>--                              (return $ InvokeIOPageTable $ IOPageTableUnmap cap cptr)
>--        _ -> throw IllegalOperation
>--decodeX64IOPTInvocation _ _ _ _ _ = fail "Unreachable"

decodeX64IOMap and decodeX64IOUnmap are combined as following function.
IOMap is related with label X64PageMapIO and IOUnmap is related with X64PageUnmap

>-- decodeX64IOFrameInvocation :: Word -> [Word] -> PPtr CTE ->
>--                    ArchCapability -> [(Capability, PPtr CTE)] ->
>--                    KernelF SyscallError ArchInv.Invocation
>-- decodeX64IOFrameInvocation label args cptr cap@(PageCap {}) extraCaps = do
>--     case (invocationType label, args, extraCaps) of
>--         (ArchInvocationLabel X64PageMapIO, rw:ioaddr:_, (iospaceCap,_):_) -> do
>--             when (not (capVPSize cap == X64SmallPage)) $
>--                 throw $ InvalidCapability 0
>--             when (isJust $ capVPMappedAddress cap) $
>--                 throw $ InvalidCapability 0
>--             (paddr,vmrights) <- case cap of
>--                 (PageCap {
>--                         capVPBasePtr = frame_pptr,
>--                         capVPRights = vmrights }) -> return (addrFromPPtr frame_pptr, vmrights)
>--                 _ -> throw $ InvalidCapability 1

>--             (deviceid,domainid) <- case iospaceCap of
>--                 ArchObjectCap (IOSpaceCap {
>--                         capIODomainID = domainid,
>--                         capIOPCIDevice = Just deviceid })
>--                     -> return (deviceid, domainid)
>--                 _ -> throw $ InvalidCapability 0
>--             pciRequestId <- withoutFailure $ pciRequestIDFromCap iospaceCap
>--             cteslot <-  withoutFailure $ lookupIOContextSlot pciRequestId
>--             cte  <- withoutFailure $ getObject cteslot
>--             (slot, level) <- case cte of
>--                 VTDCTE did rmrr aw slptr tt True -> do
>--                     let vtdpte = ptrFromPAddr slptr
>--                     lookupErrorOnFailure False $ lookupIOPTSlot vtdpte ioaddr
>--                 _ -> throw $ FailedLookup False InvalidRoot
>--             when (not (level == 0)) $
>--                 throw $ InvalidCapability 0
>--             pte <- withoutFailure $ getObject slot
>--             when (not (pte == InvalidIOPTE)) $
>--                 throw DeleteFirst
>--             let vtdpte = VTDPTE {
>--                          framePtr = paddr,
>--                          rw = getVMRights (allowRead vmrights) (allowRead (vmRightsFromBits rw)) }
>--                 cap' =  cap { capIOPTLevel = level,
>--                             capIOPTMappedAddress = Just (deviceid, VPtr ioaddr)}
>--             return $ InvokePage $ PageIOMap (ArchObjectCap cap') cptr vtdpte slot

>--         (ArchInvocationLabel X64PageMapIO, _, _) -> throw TruncatedMessage
>--         (ArchInvocationLabel X64PageUnmap, _, _) -> do
>--             (return $ InvokePage $ PageIOUnmap (ArchObjectCap cap) cptr)
>--         _ -> throw IllegalOperation
>-- decodeX64IOFrameInvocation _ _ _ _ _ = fail "Unreachable"


>-- unmapIOPage :: VMPageSize -> IOASID -> VPtr -> PPtr Word -> Kernel ()
>-- unmapIOPage sz asid ioaddr baseptr = ignoreFailure $ do
>--    cteslot <- withoutFailure $ lookupIOContextSlot asid
>--    cte <- withoutFailure $ getObject cteslot
>--    (slot, level) <- case cte of
>--        VTDCTE did rmrr aw slptr tt True ->
>--           lookupErrorOnFailure False $ lookupIOPTSlot (ptrFromPAddr slptr) (fromVPtr ioaddr)
>--        _ -> throw $ FailedLookup False InvalidRoot
>--    when (not (level == 0)) $
>--        return ()
>--    withoutFailure $ do
>--        pte <- getObject slot
>--        case pte of
>--            VTDPTE {} ->  if (framePtr pte == addrFromPPtr baseptr) then storeIOPTE slot InvalidIOPTE else return ()
>--            InvalidIOPTE -> return ()
>--        flushCacheRange slot vtdPTESizeBits
>--        doMachineOp $ invalidateIOTLB

>-- unmapIOPageTable :: Int -> IOASID -> VPtr -> PPtr IOPTE -> Kernel ()
>-- unmapIOPageTable level asid ioaddr baseptr = ignoreFailure $ do
>--    cteslot <- withoutFailure $ lookupIOContextSlot asid
>--    cte <- withoutFailure $ getObject cteslot
>--    pteslot <- case cte of
>--        VTDCTE did rmrr aw slptr tt True -> return $ ptrFromPAddr slptr
>--        _ -> throw $ FailedLookup False InvalidRoot
>--    if (level == 0)
>--        then when (addrFromPPtr pteslot == addrFromPPtr baseptr) $ withoutFailure $ do
>--            storeIOPTE pteslot InvalidIOPTE
>--            flushCacheRange pteslot vtdPTESizeBits
>--        else do
>--            (targetslot,retlvl) <-lookupErrorOnFailure False $
>--                lookupIOPTResolveLevels pteslot ((fromVPtr ioaddr) `shiftR` pageBits) (level - 1) (level - 1)
>--            withoutFailure $ do
>--                pte <- getObject targetslot
>--                case pte of
>--                    VTDPTE {} ->  if (framePtr pte == (addrFromPPtr baseptr))
>--                                     then storeIOPTE targetslot InvalidIOPTE
>--                                     else return ()
>--                    InvalidIOPTE -> return ()
>--                flushCacheRange targetslot vtdPTESizeBits
>--                doMachineOp $ invalidateIOTLB


>-- getPCIBus :: IOASID -> Word
>-- getPCIBus picRequestId = fromIntegral $ (picRequestId `shiftR` 8) .&. 0xFF


>-- getPCIDev :: IOASID -> Word
>-- getPCIDev picRequestId = fromIntegral $ (picRequestId `shiftR` 3) .&. 0x1F

>-- getPCIFun :: IOASID -> Word
>-- getPCIFun picRequestId = fromIntegral $ picRequestId .&. 0x7

>-- getPCIRequestId :: Word -> Word -> Word -> IOASID
>-- getPCIRequestId bus dev fun = fromIntegral $ (bus `shiftL` 8) .|. (dev `shiftL` 3) .|. fun


%-- x86KSnumIOPTLevels is computed via vtd_init and is of type uint_32.
%-- However x86KSnumIOPTLevels in haskell is hardcoded so far.

>-- getVTDPTEOffset :: Word -> Int -> Int -> Word
>-- getVTDPTEOffset translation levelsToResolve levelsRemaining =
>--     let lvldiff = levelsToResolve - levelsRemaining
>--     in (translation `shiftR` (vtdPTBits * (x86KSnumIOPTLevels - 1 - lvldiff))) .&. (mask vtdPTBits)

>-- pciRequestIDFromCap :: Capability -> Kernel IOASID
>-- pciRequestIDFromCap cap = case cap of
>--     ArchObjectCap (IOSpaceCap _ (Just pcidev)) -> return pcidev
>--     ArchObjectCap (IOPageTableCap ioptbase _ (Just (ioasid,vptr))) -> return ioasid
>--     ArchObjectCap (PageCap _ _ _ _ _ (Just (ioasid, vptr))) -> return $ fromIntegral $ ioasid
>--     _ -> fail "Invalid cap type"


>-- x86KSvtdRootTable :: Word
>-- x86KSvtdRootTable = 0 -- FIXME: this is not correct, similar to ipcbuf, artifical hard coded address not good, and I don't want do that again here.

>-- lookupIOContextSlot :: IOASID -> Kernel (PPtr IOCTE)
>-- lookupIOContextSlot pciRequestId = do
>--     rootIndex <- return $ getPCIBus pciRequestId
>--     rtePtr <- return $ PPtr $ x86KSvtdRootTable + rootIndex
>--     rte <- getObject rtePtr
>--     case rte of
>--         VTDRTE {} -> do
>--             let cteTablePtr = ptrFromPAddr $ cxtTablePtr rte
>--             let cteIndex = ((getPCIDev pciRequestId) `shiftL` vtdCTESizeBits) .|. getPCIFun(pciRequestId)
>--             let ctePtr = cteTablePtr + (PPtr $ cteIndex `shiftL` vtdCTESizeBits)
>--             return $ ctePtr
>--         _ -> fail "Invalid rte in lookupIOContextSlot"

>-- lookupIOPTResolveLevels :: PPtr IOPTE -> Word -> Int -> Int -> KernelF LookupFailure (PPtr IOPTE, Int)
>-- lookupIOPTResolveLevels vtdpte translation levelsToResolve levelsRemaining = do
>--     ptePtr <- return $ vtdpte + (PPtr $ getVTDPTEOffset translation levelsToResolve levelsRemaining)
>--     if (levelsRemaining == 0) then return (ptePtr,0) else do
>--       iopte <- withoutFailure $ getObject ptePtr
>--       case iopte of
>--         VTDPTE framePtr rw -> do
>--           let slot = ptrFromPAddr (framePtr)
>--           if (not $ rw == VMReadWrite) then return (ptePtr, levelsRemaining)
>--                     else lookupIOPTResolveLevels slot translation levelsToResolve (levelsRemaining - 1)
>--         _ -> throw $ MissingCapability levelsRemaining

>-- lookupIOPTSlot :: PPtr IOPTE -> Word -> KernelF LookupFailure (PPtr IOPTE, Int)
>-- lookupIOPTSlot vtdpte ioaddr = lookupIOPTResolveLevels vtdpte (ioaddr `shiftR` pageBits) (x86KSnumIOPTLevels - 1) (x86KSnumIOPTLevels - 1)


>-- invalidateIOTLB = error "Not implemented"

>-- unmapVTDCTE :: Capability -> Kernel ()
>-- unmapVTDCTE cap = do
>--      pciRequestId <- pciRequestIDFromCap cap
>--      cte_ptr <- lookupIOContextSlot pciRequestId
>--      storeIOCTE cte_ptr InvalidIOCTE
>--      flushCacheRange cte_ptr vtdCTESizeBits
>--      doMachineOp $ invalidateIOTLB -}

> decodeX64PDPointerTableInvocation :: Word -> [Word] -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation

> decodeX64PDPointerTableInvocation label args cte cap@(PDPointerTableCap {}) extraCaps = do
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel X64PDPTMap, vaddr':attr:_, (vspaceCap,_):_) -> do
>             when (isJust $ capPDPTMappedAddress cap) $
>                 throw $ InvalidCapability 0
>             (vspace,asid) <- case vspaceCap of
>                 ArchObjectCap (PML4Cap {
>                          capPML4MappedASID = Just asid,
>                          capPML4BasePtr = vspace })
>                     -> return (vspace,asid)
>                 _ -> throw $ InvalidCapability 1
>             let vaddr = vaddr' .&. complement (mask pml4ShiftBits)
>             when (VPtr vaddr > VPtr userVTop ) $
>                 throw $ InvalidArgument 0
>             vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
>             when (vspaceCheck /= vspace) $ throw $ InvalidCapability 1
>             let pml4Slot = lookupPML4Slot vspace (VPtr vaddr)
>             oldpml4e <- withoutFailure $ getObject pml4Slot
>             unless (oldpml4e == InvalidPML4E) $ throw DeleteFirst
>             let pml4e = PDPointerTablePML4E {
>                     pml4eTable = addrFromPPtr $ capPDPTBasePtr cap,
>                     pml4eAccessed = False,
>                     pml4eCacheDisabled = x64CacheDisabled $ attribsFromWord attr,
>                     pml4eWriteThrough = x64WriteThrough $ attribsFromWord attr,
>                     pml4eExecuteDisable = False,
>                     pml4eRights = VMReadWrite }
>             return $ InvokePDPT $ PDPTMap {
>                 pdptMapCap = ArchObjectCap $ cap { capPDPTMappedAddress = Just (asid, (VPtr vaddr)) },
>                 pdptMapCTSlot = cte,
>                 pdptMapPML4E = pml4e,
>                 pdptMapPML4Slot = pml4Slot,
>                 pdptMapVSpace = vspace }
>         (ArchInvocationLabel X64PDPTMap, _, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64PDPTUnmap, _, _) -> do
>             cteVal <- withoutFailure $ getCTE cte
>             final <- withoutFailure $ isFinalCapability cteVal
>             unless final $ throw RevokeFirst
>             return $ InvokePDPT $ PDPTUnmap {
>                 pdptUnmapCap = cap,
>                 pdptUnmapCapSlot = cte }
>         _ -> throw IllegalOperation
> decodeX64PDPointerTableInvocation _ _ _ _ _ = fail "Unreachable"


> decodeX64PageDirectoryInvocation :: Word -> [Word] -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation

> decodeX64PageDirectoryInvocation label args cte cap@(PageDirectoryCap {}) extraCaps  =
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel X64PageDirectoryMap, vaddr':attr:_, (pml4Cap,_):_) -> do
>             when (isJust $ capPDMappedAddress cap) $
>                 throw $ InvalidCapability 0
>             (pml,asid) <- case pml4Cap of
>                 ArchObjectCap (PML4Cap {
>                          capPML4MappedASID = Just asid,
>                          capPML4BasePtr = pml })
>                     -> return (pml,asid)
>                 _ -> throw $ InvalidCapability 1
>             let vaddr = vaddr' .&. complement (mask pdptShiftBits)
>             when (VPtr vaddr > VPtr userVTop ) $
>                 throw $ InvalidArgument 0
>             pmlCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
>             when (pmlCheck /= pml) $ throw $ InvalidCapability 1
>             pdptSlot <- lookupErrorOnFailure False $ lookupPDPTSlot pml (VPtr vaddr)
>             oldpde <- withoutFailure $ getObject pdptSlot
>             unless (oldpde == InvalidPDPTE) $ throw DeleteFirst
>             let pdpte = PageDirectoryPDPTE {
>                     pdpteTable = addrFromPPtr $ capPDBasePtr cap,
>                     pdpteAccessed = False,
>                     pdpteCacheDisabled = x64CacheDisabled $ attribsFromWord attr,
>                     pdpteWriteThrough = x64WriteThrough $ attribsFromWord attr,
>                     pdpteExecuteDisable = False,
>                     pdpteRights = VMReadWrite }
>             return $ InvokePageDirectory $ PageDirectoryMap {
>                 pdMapCap = ArchObjectCap $ cap { capPDMappedAddress = Just (asid, (VPtr vaddr)) },
>                 pdMapCTSlot = cte,
>                 pdMapPDPTE = pdpte,
>                 pdMapPDPTSlot = pdptSlot,
>                 pdMapVSpace = pml }
>         (ArchInvocationLabel X64PageDirectoryMap, _, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64PageDirectoryUnmap, _, _) -> do
>             cteVal <- withoutFailure $ getCTE cte
>             final <- withoutFailure $ isFinalCapability cteVal
>             unless final $ throw RevokeFirst
>             return $ InvokePageDirectory $ PageDirectoryUnmap {
>                 pdUnmapCap = cap,
>                 pdUnmapCapSlot = cte }
>         _ -> throw IllegalOperation
> decodeX64PageDirectoryInvocation _ _ _ _ _ = fail "Unreachable"


> decodeX64PageTableInvocation :: Word -> [Word] -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation

> decodeX64PageTableInvocation label args cte cap@(PageTableCap {}) extraCaps =
>    case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel X64PageTableMap, vaddr':attr:_, (pml4Cap,_):_) -> do
>             when (isJust $ capPTMappedAddress cap) $
>                 throw $ InvalidCapability 0
>             (pml,asid) <- case pml4Cap of
>                 ArchObjectCap (PML4Cap {
>                          capPML4MappedASID = Just asid,
>                          capPML4BasePtr = pml })
>                     -> return (pml,asid)
>                 _ -> throw $ InvalidCapability 1
>             let vaddr = vaddr' .&. complement (mask pdShiftBits)
>             when (VPtr vaddr > VPtr userVTop ) $
>                 throw $ InvalidArgument 0
>             pmlCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
>             when (pmlCheck /= pml) $ throw $ InvalidCapability 1
>             pdSlot <- lookupErrorOnFailure False $ lookupPDSlot pml (VPtr vaddr)
>             oldpde <- withoutFailure $ getObject pdSlot
>             unless (oldpde == InvalidPDE) $ throw DeleteFirst
>             let pde = PageTablePDE {
>                     pdeTable = addrFromPPtr $ capPTBasePtr cap,
>                     pdeAccessed = False,
>                     pdeCacheDisabled = x64CacheDisabled $ attribsFromWord attr,
>                     pdeWriteThrough = x64WriteThrough $ attribsFromWord attr,
>                     pdeExecuteDisable = False,
>                     pdeRights = VMReadWrite}
>             return $ InvokePageTable $ PageTableMap {
>                 ptMapCap = ArchObjectCap $ cap { capPTMappedAddress = Just (asid, (VPtr vaddr)) },
>                 ptMapCTSlot = cte,
>                 ptMapPDE = pde,
>                 ptMapPDSlot = pdSlot,
>                 ptMapVSpace = pml }
>         (ArchInvocationLabel X64PageTableMap, _, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64PageTableUnmap, _, _) -> do
>             cteVal <- withoutFailure $ getCTE cte
>             final <- withoutFailure $ isFinalCapability cteVal
>             unless final $ throw RevokeFirst
>             return $ InvokePageTable $ PageTableUnmap {
>                 ptUnmapCap = cap,
>                 ptUnmapCapSlot = cte }
>         _ -> throw IllegalOperation
> decodeX64PageTableInvocation _ _ _ _ _ = fail "Unreachable"


> decodeX64ASIDControlInvocation :: Word -> [Word] ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation

> decodeX64ASIDControlInvocation label args ASIDControlCap extraCaps =
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel X64ASIDControlMakePool, index:depth:_,
>                         (untyped,parentSlot):(croot,_):_) -> do
>             asidTable <- withoutFailure $ gets (x64KSASIDTable . ksArchState)
>             let free = filter (\(x,y) -> x <= (1 `shiftL` asidHighBits) - 1 && isNothing y) $ assocs asidTable
>             when (null free) $ throw DeleteFirst
>             let base = (fst $ head free) `shiftL` asidLowBits
>             let pool = makeObject :: ASIDPool
>             frame <- case untyped of
>                 UntypedCap { capIsDevice = False } | capBlockSize untyped == objBits pool -> do
>                     ensureNoChildren parentSlot
>                     return $ capPtr untyped
>                 _ -> throw $ InvalidCapability 1
>             destSlot <- lookupTargetSlot croot (CPtr index) (fromIntegral depth)
>             ensureEmptySlot destSlot
>             return $ InvokeASIDControl $ MakePool {
>                 makePoolFrame = frame,
>                 makePoolSlot = destSlot,
>                 makePoolParent = parentSlot,
>                 makePoolBase = base }
>         (ArchInvocationLabel X64ASIDControlMakePool, _, _) -> throw TruncatedMessage
>         _ -> throw IllegalOperation
> decodeX64ASIDControlInvocation _ _ _ _ = fail "Unreachable"


> decodeX64ASIDPoolInvocation :: Word ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation

> decodeX64ASIDPoolInvocation label cap@(ASIDPoolCap {}) extraCaps =
>     case (invocationType label, extraCaps) of
>         (ArchInvocationLabel X64ASIDPoolAssign, (vspaceCap,vspaceCapSlot):_) ->
>             case vspaceCap of
>                 ArchObjectCap (PML4Cap { capPML4MappedASID = Nothing })
>                   -> do
>                     asidTable <- withoutFailure $ gets (x64KSASIDTable . ksArchState)
>                     let base = capASIDBase cap
>                     let poolPtr = asidTable!(asidHighBitsOf base)
>                     when (isNothing poolPtr) $ throw $ FailedLookup False InvalidRoot
>                     let Just p = poolPtr
>                     when (p /= capASIDPool cap) $ throw $ InvalidCapability 0
>                     ASIDPool pool <- withoutFailure $ getObject $ p
>                     let free = filter (\(x,y) -> x <=  (1 `shiftL` asidLowBits) - 1
>                                                  && x + base /= 0 && isNothing y) $ assocs pool
>                     when (null free) $ throw DeleteFirst
>                     let asid = fst $ head free
>                     return $ InvokeASIDPool $ Assign {
>                         assignASID = asid + base,
>                         assignASIDPool = capASIDPool cap,
>                         assignASIDCTSlot = vspaceCapSlot }
>                 _ -> throw $ InvalidCapability 1
>         (ArchInvocationLabel X64ASIDPoolAssign, _) -> throw TruncatedMessage
>         _ -> throw IllegalOperation
> decodeX64ASIDPoolInvocation _ _ _ = fail "Unreachable"



> decodeX64MMUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation

> decodeX64MMUInvocation label args _ cte cap@(PageCap {}) extraCaps =
>  decodeX64FrameInvocation label args cte cap extraCaps
> decodeX64MMUInvocation label args _ cte cap@(PDPointerTableCap {}) extraCaps =
>  decodeX64PDPointerTableInvocation label args cte cap extraCaps
> decodeX64MMUInvocation label args _ cte cap@(PageDirectoryCap {}) extraCaps =
>  decodeX64PageDirectoryInvocation label args cte cap extraCaps
> decodeX64MMUInvocation label args _ cte cap@(PageTableCap {}) extraCaps =
>  decodeX64PageTableInvocation label args cte cap extraCaps
> decodeX64MMUInvocation label args _ _ cap@(ASIDControlCap {}) extraCaps =
>  decodeX64ASIDControlInvocation label args cap extraCaps
> decodeX64MMUInvocation label _ _ _ cap@(ASIDPoolCap {}) extraCaps =
>  decodeX64ASIDPoolInvocation label cap extraCaps
> decodeX64MMUInvocation _ _ _ _ (PML4Cap {}) _ = throw IllegalOperation
>-- decodeX64MMUInvocation label args _ cte cap@(IOPageTableCap {}) extraCaps =
>--  decodeX64IOPTInvocation label args cte cap extraCaps
> decodeX64MMUInvocation _ _ _ _ _ _ = fail "Unreachable"


Checking virtual address for page size dependent alignment:

> checkVPAlignment :: VMPageSize -> VPtr -> KernelF SyscallError ()
>
> checkVPAlignment sz w =
>     unless (w .&. mask (pageBitsForSize sz) == 0) $
>            throw AlignmentError

> checkValidMappingSize :: VMPageSize -> Kernel ()
> checkValidMappingSize _ = return ()

\subsection{Invocation Implementations}

> performX64MMUInvocation :: ArchInv.Invocation -> KernelP [Word]
> performX64MMUInvocation i = withoutPreemption $ do
>     case i of
>         InvokePDPT oper -> do
>             performPDPTInvocation oper
>             return []
>         InvokePageDirectory oper -> do
>             performPageDirectoryInvocation oper
>             return []
>         InvokePageTable oper -> do
>             performPageTableInvocation oper
>             return []
>--         InvokeIOPageTable oper -> performIOPageTableInvocation oper
>         InvokePage oper -> performPageInvocation oper
>         InvokeASIDControl oper -> do
>             performASIDControlInvocation oper
>             return []
>         InvokeASIDPool oper -> do
>             performASIDPoolInvocation oper
>             return []
>         _ -> fail "Unreachable"

> performPDPTInvocation :: PDPTInvocation -> Kernel ()
> performPDPTInvocation (PDPTMap cap ctSlot pml4e pml4Slot vspace) = do
>     updateCap ctSlot cap
>     storePML4E pml4Slot pml4e
>     asid <- case cap of
>             ArchObjectCap (PDPointerTableCap _ (Just (a, _))) -> return a
>             _ -> fail "should never happen"
>     invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
>
> performPDPTInvocation (PDPTUnmap cap ctSlot) = do
>     case capPDPTMappedAddress cap of
>         Just (asid, vaddr) -> do
>             unmapPDPT asid vaddr (capPDPTBasePtr cap)
>             let ptr = capPDPTBasePtr cap
>             let pdpteBits = objBits InvalidPDPTE
>             let slots = [ptr, ptr + bit pdpteBits .. ptr + bit pdptBits - 1]
>             mapM_ (flip storePDPTE InvalidPDPTE) slots
>         _ -> return ()
>     ArchObjectCap cap <- getSlotCap ctSlot
>     updateCap ctSlot (ArchObjectCap $ cap { capPDPTMappedAddress = Nothing })

> performPageDirectoryInvocation :: PageDirectoryInvocation -> Kernel ()
> performPageDirectoryInvocation (PageDirectoryMap cap ctSlot pdpte pdptSlot vspace) = do
>     updateCap ctSlot cap
>     storePDPTE pdptSlot pdpte
>     asid <- case cap of
>             ArchObjectCap (PageDirectoryCap _ (Just (a, _))) -> return a
>             _ -> fail "should never happen"
>     invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
>
> performPageDirectoryInvocation (PageDirectoryUnmap cap ctSlot) = do
>     case capPDMappedAddress cap of
>         Just (asid, vaddr) -> do
>             unmapPageDirectory asid vaddr (capPDBasePtr cap)
>             let ptr = capPDBasePtr cap
>             let pdeBits = objBits InvalidPDE
>             let slots = [ptr, ptr + bit pdeBits .. ptr + bit pdBits - 1]
>             mapM_ (flip storePDE InvalidPDE) slots
>         _ -> return ()
>     ArchObjectCap cap <- getSlotCap ctSlot
>     updateCap ctSlot (ArchObjectCap $ cap { capPDMappedAddress = Nothing })


> performPageTableInvocation :: PageTableInvocation -> Kernel ()
> performPageTableInvocation (PageTableMap cap ctSlot pde pdSlot vspace) = do
>     updateCap ctSlot cap
>     storePDE pdSlot pde
>     asid <- case cap of
>             ArchObjectCap (PageTableCap _ (Just (a, _))) -> return a
>             _ -> fail "should never happen"
>     invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
>
> performPageTableInvocation (PageTableUnmap cap slot) = do
>     case capPTMappedAddress cap of
>         Just (asid, vaddr) -> do
>             unmapPageTable asid vaddr (capPTBasePtr cap)
>             let ptr = capPTBasePtr cap
>             let pteBits = objBits InvalidPTE
>             let slots = [ptr, ptr + bit pteBits .. ptr + bit ptBits - 1]
>             mapM_ (flip storePTE InvalidPTE) slots
>         _ -> return ()
>     ArchObjectCap cap <- getSlotCap slot
>     updateCap slot (ArchObjectCap $ cap { capPTMappedAddress = Nothing })

>-- performIOPageTableInvocation :: IOPageTableInvocation -> Kernel ()
>-- performIOPageTableInvocation (IOPageTableMap cap cptr vtdpte slot) = do
>--     storeIOPTE slot vtdpte
>--     flushCacheRange slot vtdPTESizeBits
>--     updateCap cptr (ArchObjectCap cap)

>-- performIOPageTableInvocation (IOPageTableMapContext cap cptr vtdcte slot) = do
>--     storeIOCTE slot vtdcte
>--     flushCacheRange slot vtdCTESizeBits
>--     updateCap cptr (ArchObjectCap cap)

>-- performIOPageTableInvocation (IOPageTableUnmap cap cptr) = do
>--     deleteIOPageTable cap
>--     ArchObjectCap cap <- getSlotCap cptr
>--     updateCap cptr (ArchObjectCap $
>--                           cap { capVPMappedAddress = Nothing }) -}


> pteCheckIfMapped :: PPtr PTE -> Kernel Bool
> pteCheckIfMapped slot = do
>     pt <- getObject slot
>     return $ pt /= InvalidPTE

> pdeCheckIfMapped :: PPtr PDE -> Kernel Bool
> pdeCheckIfMapped slot = do
>     pd <- getObject slot
>     return $ pd /= InvalidPDE

> performPageInvocation :: PageInvocation -> Kernel [Word]
> performPageInvocation (PageMap cap ctSlot entries vspace) = do
>     updateCap ctSlot cap
>     case entries of
>         (VMPTE pte, VMPTEPtr slot) -> storePTE slot pte
>         (VMPDE pde, VMPDEPtr slot) -> storePDE slot pde
>         (VMPDPTE pdpte, VMPDPTEPtr slot) -> storePDPTE slot pdpte
>         _ -> fail "impossible"
>     asid <- case cap of
>         ArchObjectCap (PageCap _ _ _ _ _ (Just (as, _))) -> return as
>         _ -> fail "impossible"
>     invalidatePageStructureCacheASID (addrFromPPtr vspace) asid
>     return []
>
> performPageInvocation (PageUnmap cap ctSlot) = do
>     when (isJust $ capVPMappedAddress cap) $ case capVPMapType cap of
>         VMVSpaceMap -> do
>             performPageInvocationUnmap cap ctSlot
>         _ -> fail "mapped cap has incorrect map type"
>     return []

>-- performPageInvocation (PageIOMap cap cptr vtdpte slot) = do
>--     updateCap cptr cap
>--     storeIOPTE slot vtdpte
>--     return []
>--
>-- performPageInvocation (PageIOUnmap (ArchObjectCap cap@PageCap {}) ctSlot) = do
>--     case capVPMappedAddress cap of
>--         Just (asid, vaddr) -> unmapIOPage (capVPSize cap) (fromIntegral asid) vaddr
>--                                     (capVPBasePtr cap)
>--         _ -> return ()
>--     ArchObjectCap cap <- getSlotCap ctSlot
>--     updateCap ctSlot (ArchObjectCap $
>--                           cap { capVPMappedAddress = Nothing })
>--     return []
>-- performPageInvocation (PageIOUnmap _ _)  = fail "impossible" -}
>
> performPageInvocation (PageGetAddr ptr) = do
>     return [fromPAddr $ addrFromPPtr ptr]

> performPageInvocationUnmap :: ArchCapability -> PPtr CTE -> Kernel ()
> performPageInvocationUnmap cap ctSlot = do
>     case capVPMappedAddress cap of
>         Just (asid, vaddr) -> unmapPage (capVPSize cap) asid vaddr
>                                     (capVPBasePtr cap)
>         _ -> return ()
>     ArchObjectCap cap <- getSlotCap ctSlot
>     updateCap ctSlot (ArchObjectCap $
>                           cap { capVPMappedAddress = Nothing,
>                                 capVPMapType = VMNoMap })

> performASIDControlInvocation :: ASIDControlInvocation -> Kernel ()
> performASIDControlInvocation (MakePool frame slot parent base) = do
>     deleteObjects frame pageBits
>     pcap <- getSlotCap parent
>     updateFreeIndex parent (maxFreeIndex (capBlockSize pcap))
>     placeNewObject frame (makeObject :: ASIDPool) 0
>     let poolPtr = PPtr $ fromPPtr frame
>     cteInsert (ArchObjectCap $ ASIDPoolCap poolPtr base) parent slot
>     assert (asidLowBitsOf base == 0)
>         "ASID pool's base must be aligned"
>     asidTable <- gets (x64KSASIDTable . ksArchState)
>     let asidTable' = asidTable//[(asidHighBitsOf base, Just poolPtr)]
>     modify (\s -> s {
>         ksArchState = (ksArchState s) { x64KSASIDTable = asidTable' }})


> performASIDPoolInvocation :: ASIDPoolInvocation -> Kernel ()
> performASIDPoolInvocation (Assign asid poolPtr ctSlot) = do
>     oldcap <- getSlotCap ctSlot
>     let ArchObjectCap cap = oldcap
>     updateCap ctSlot (ArchObjectCap $ cap { capPML4MappedASID = Just asid })
>     ASIDPool pool <- getObject poolPtr
>     let pool' = pool//[(asidLowBitsOf asid, Just $ capPML4BasePtr cap)]
>     setObject poolPtr $ ASIDPool pool'

\subsection{Simulator Support}

The kernel model's x64 targets use an external simulation of the physical address space for user-level virtual memory, I/O devices and MMU data structures, separate from the "PSpace" which is used for kernel objects. However, "PDE" objects are accessed by the kernel, so they must be stored in both the external physical memory model and the internal "PSpace". To make verification simpler we do the same for "PTE" objects.

> storePML4E :: PPtr PML4E -> PML4E -> Kernel ()
> storePML4E slot pml4e = do
>     setObject slot pml4e
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPML4E pml4e

> storePDPTE :: PPtr PDPTE -> PDPTE -> Kernel ()
> storePDPTE slot pdpte = do
>     setObject slot pdpte
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPDPTE pdpte


> storePDE :: PPtr PDE -> PDE -> Kernel ()
> storePDE slot pde = do
>     setObject slot pde
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPDE pde


> storePTE :: PPtr PTE -> PTE -> Kernel ()
> storePTE slot pte = do
>     setObject slot pte
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPTE pte

>-- storeIOCTE :: PPtr IOCTE -> IOCTE -> Kernel ()
>-- storeIOCTE slot cte = do
>--     setObject slot cte
>--     (high,low) <- return $ wordFromIOCTE cte
>--     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) high
>--     doMachineOp $ storeWordVM (8 + (PPtr $ fromPPtr slot)) low


>-- storeIOPTE :: PPtr IOPTE -> IOPTE -> Kernel ()
>-- storeIOPTE slot pte = do
>--     setObject slot pte
>--     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromIOPTE pte


%-- The first 64 bits of rte is ignored

>-- storeIORTE :: PPtr IORTE -> IORTE -> Kernel ()
>-- storeIORTE slot rte = do
>--     setObject slot rte
>--     doMachineOp $ storeWordVM (8 + (PPtr $ fromPPtr slot)) $ wordFromIORTE rte

>-- deleteIOPageTable :: ArchCapability -> Kernel ()
>-- deleteIOPageTable (cap@IOPageTableCap {}) =
>--     case capIOPTMappedAddress cap of
>--         Just (asid, vaddr) -> unmapIOPageTable (capIOPTLevel cap) asid vaddr
>--                                     (capIOPTBasePtr cap)
>--         _ -> return ()

>-- deleteIOPageTable _ = error "Not an IOPageTable capability" -}

> mapKernelWindow  :: Kernel ()
> mapKernelWindow = error "boot code unimplemented"

> activateGlobalVSpace :: Kernel ()
> activateGlobalVSpace = error "boot code unimplemented"

> createIPCBufferFrame :: Capability -> VPtr -> KernelInit Capability
> createIPCBufferFrame = error "boot code unimplemented"

> createBIFrame :: Capability -> VPtr -> Word32 -> Word32 -> KernelInit Capability
> createBIFrame = error "boot code unimplemented"

> createFramesOfRegion :: Capability -> Region -> Bool -> KernelInit ()
> createFramesOfRegion = error "boot code unimplemented"

> createITPDPTs :: Capability -> VPtr -> VPtr -> KernelInit Capability
> createITPDPTs  = error "boot code unimplemented"

> writeITPDPTs :: Capability -> Capability -> KernelInit ()
> writeITPDPTs  = error "boot code unimplemented"

> createITASIDPool :: Capability -> KernelInit Capability
> createITASIDPool  = error "boot code unimplemented"

> writeITASIDPool :: Capability -> Capability -> Kernel ()
> writeITASIDPool  = error "boot code unimplemented"

> createDeviceFrames :: Capability -> KernelInit ()
> createDeviceFrames  = error "boot code unimplemented"

> vptrFromPPtr :: PPtr a -> KernelInit VPtr
> vptrFromPPtr  = error "boot code unimplemented"


