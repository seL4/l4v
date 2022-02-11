--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the handling of the RISC-V hardware-defined page tables.

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.
-- Progress: added VCPU cases (uninteresting)

-- FIXME AARCH64: added HW ASID helpers and adjusted findVSpaceForASID

module SEL4.Kernel.VSpace.AARCH64 where

import Prelude hiding (Word)
import SEL4.API.Types
import SEL4.API.Failures
import SEL4.API.Failures.AARCH64
import SEL4.Machine.RegisterSet
import SEL4.Machine.RegisterSet.AARCH64 (Register(..))
import SEL4.Machine.Hardware.AARCH64
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Model.StateData.AARCH64
import SEL4.API.InvocationLabels
import SEL4.API.InvocationLabels.AARCH64
import {-# SOURCE #-} SEL4.Object.CNode
import {-# SOURCE #-} SEL4.Object.TCB
import {-# SOURCE #-} SEL4.Kernel.Init
import {-# SOURCE #-} SEL4.Kernel.CSpace
import SEL4.Object.VCPU.AARCH64

import Data.Bits
import Data.Maybe
import Data.Array
import Data.List
import Data.Word (Word32)

-- The AArch64-specific invocations are imported with the "ArchInv" prefix. This
-- is necessary to avoid namespace conflicts with the generic invocations.

import SEL4.API.Invocation.AARCH64 as ArchInv

{- Constants -}

ipcBufferSizeBits :: Int
ipcBufferSizeBits = 10

{- Lookups and Faults -}

{- IPC Buffer Accesses -}

-- physical address of the IPC buffer, if it is accessible
lookupIPCBuffer :: Bool -> PPtr TCB -> Kernel (Maybe (PPtr Word))
lookupIPCBuffer isReceiver thread = do
    bufferPtr <- threadGet tcbIPCBuffer thread
    bufferFrameSlot <- getThreadBufferSlot thread
    bufferCap <- getSlotCap bufferFrameSlot
    case bufferCap of
        ArchObjectCap (FrameCap {capFIsDevice = False, capFBasePtr = basePtr,
                                 capFVMRights = rights, capFSize = sz}) -> do
            let pBits = pageBitsForSize sz
            if (rights == VMReadWrite || not isReceiver && rights == VMReadOnly)
                then do
                    let ptr = basePtr + PPtr (fromVPtr bufferPtr .&. mask pBits)
                    assert (ptr /= 0) "IPC buffer pointer must be non-null"
                    return $ Just ptr
                else return Nothing
        _ -> return Nothing

{- ASID Lookups -}

-- FIXME AARCH64: make this a Reader Monad
getPoolPtr :: ASID -> Kernel (Maybe (PPtr ASIDPool))
getPoolPtr asid = do
    assert (asid > 0) "ASID 0 is used for objects that are not mapped"
    assert (asid <= snd asidRange) "ASID out of range"
    asidTable <- gets (armKSASIDTable . ksArchState)
    return $ asidTable!(asidHighBitsOf asid)

-- FIXME AARCH64: make this a Reader Monad
getASIDPoolEntry :: ASID -> Kernel (Maybe ASIDPoolEntry)
getASIDPoolEntry asid = do
    poolPtr <- getPoolPtr asid
    maybePool <- case poolPtr of
        Just ptr -> liftM Just $ getObject ptr
        Nothing -> return Nothing
    case maybePool of
        Just (ASIDPool pool) -> return $ pool!(asid .&. mask asidLowBits)
        Nothing -> return Nothing

updateASIDPoolEntry :: (ASIDPoolEntry -> Maybe ASIDPoolEntry) -> ASID -> Kernel ()
updateASIDPoolEntry f asid = do
    maybePoolPtr <- getPoolPtr asid
    assert (isJust maybePoolPtr) "ASID pool pointer must exist"
    let poolPtr = fromJust maybePoolPtr
    ASIDPool pool <- getObject poolPtr
    let maybeEntry = pool!(asid .&. mask asidLowBits)
    assert (isJust maybeEntry) "ASID pool entry must exist"
    let pool' = pool//[(asid .&. mask asidLowBits, f $ fromJust maybeEntry)]
    setObject poolPtr $ ASIDPool pool'

findVSpaceForASID :: ASID -> KernelF LookupFailure (PPtr PTE)
findVSpaceForASID asid = do
    maybeEntry <- withoutFailure $ getASIDPoolEntry asid
    case maybeEntry of
        Just (ASIDPoolVSpace vmID ptr) -> do
            assert (ptr /= 0) "findVSpaceForASID: found null PD"
            withoutFailure $ checkPTAt ptr
            return ptr
        _ -> throw $ InvalidRoot

maybeVSpaceForASID :: ASID -> Kernel (Maybe (PPtr PTE))
maybeVSpaceForASID asid =
    liftM Just (findVSpaceForASID asid) `catchFailure` const (return Nothing)

-- used in proofs only, will be translated to ptable_at.
checkPTAt :: PPtr PTE -> Kernel ()
checkPTAt _ = return ()


{- Locating Page Table Slots -}

isPageTablePTE :: PTE -> Bool
isPageTablePTE (PageTablePTE {}) = True
isPageTablePTE _ = False

isPagePTE :: PTE -> Bool
isPagePTE (PagePTE {}) = True
isPagePTE _ = False

-- FIXME AARCH64: replace name with whatever ppns will be called
-- only used on non-toplevel tables
pteAddr :: PTE -> PAddr
pteAddr pte = ptePPN pte `shiftL` ptBits False

getPPtrFromHWPTE :: PTE -> PPtr PTE
getPPtrFromHWPTE pte = ptrFromPAddr $ pteAddr pte

-- how many bits there are left to be translated at a given level (0 = bottom
-- level). This counts the bits the levels below the current one translate, so
-- no case distinction needed for the top level -- it never participates.
-- Example: if maxPTLevel = 2, and we are on level 2, that means level 0 and 1
-- are below us and we still need translate the bits for level 0 and 1 after
-- this lookup, but not the ones from level 2, so only level 0 and 1 need to be
-- counted in ptBitsLeft.
ptBitsLeft :: Int -> Int
ptBitsLeft level = ptTranslationBits False * level + pageBits

-- compute index into a page table from vPtr at given level
ptIndex :: Int -> VPtr -> Word
ptIndex level vPtr =
    (fromVPtr vPtr `shiftR` ptBitsLeft level) .&. mask (ptTranslationBits (level == maxPTLevel))

-- compute slot ptr inside the table ptPtr at given level for a vPtr
ptSlotIndex :: Int -> PPtr PTE -> VPtr -> PPtr PTE
ptSlotIndex level ptPtr vPtr =
    ptPtr + PPtr (ptIndex level vPtr `shiftL` pteBits)

-- Look up the pte in the table ptPtr at given level with index computed from
-- vPtr for that level.
pteAtIndex :: Int -> PPtr PTE -> VPtr -> Kernel PTE
pteAtIndex level ptPtr vPtr = getObject (ptSlotIndex level ptPtr vPtr)

-- We are counting levels down instead of up, i.e. level maxPTLevel is the
-- top-level page table, and level 0 is the bottom level that contains only
-- pages or invalid entries.
lookupPTSlotFromLevel :: Int -> PPtr PTE -> VPtr -> Kernel (Int, PPtr PTE)
lookupPTSlotFromLevel 0 ptPtr vPtr =
    return (ptBitsLeft 0, ptSlotIndex 0 ptPtr vPtr)
lookupPTSlotFromLevel level ptPtr vPtr = do
    pte <- pteAtIndex level ptPtr vPtr
    if isPageTablePTE pte
        then do
            checkPTAt (getPPtrFromHWPTE pte)
            lookupPTSlotFromLevel (level-1) (getPPtrFromHWPTE pte) vPtr
        else return (ptBitsLeft level, ptSlotIndex level ptPtr vPtr)

-- lookupPTSlot walks the page table and returns a pointer to the slot that maps
-- a given virtual address, together with the number of bits left to translate,
-- indicating the size of the frame.
lookupPTSlot :: PPtr PTE -> VPtr -> Kernel (Int, PPtr PTE)
lookupPTSlot = lookupPTSlotFromLevel maxPTLevel

lookupFrame :: PPtr PTE -> VPtr -> Kernel (Maybe (Int, PAddr))
lookupFrame vspaceRoot vPtr = do
    (bitsLeft, ptePtr) <- lookupPTSlot vspaceRoot vPtr
    pte <- getObject ptePtr
    if isPagePTE pte
        then return $ Just (bitsLeft, pteAddr pte)
        else return Nothing

{- Page Table Modification -}

{- Handling Faults -}

handleVMFault :: PPtr TCB -> VMFaultType -> KernelF Fault ()
handleVMFault _ ARMDataAbort = do
    addr <- withoutFailure $ doMachineOp getFAR
    fault <- withoutFailure $ doMachineOp getDFSR
    active <- withoutFailure $ curVCPUActive
    addr <- if active
            then do
                -- FIXME AARCH64: assumes GET_PAR_ADDR is inside addressTranslateS1
                addr' <- withoutFailure $ doMachineOp $ addressTranslateS1 addr
                return $ addr' .|. (addr .&. mask pageBits)
            else
                return addr
    -- 32 is the width of the FSR field in the C VMFault structure:
    throw $ ArchFault $ VMFault addr [0, fault .&. mask 32]

handleVMFault thread ARMPrefetchAbort = do
    pc <- withoutFailure $ asUser thread $ getRestartPC
    fault <- withoutFailure $ doMachineOp getIFSR
    active <- withoutFailure $ curVCPUActive
    pc <- if active
          then do
              -- FIXME AARCH64: assumes GET_PAR_ADDR is inside addressTranslateS1
              pc' <- withoutFailure $ doMachineOp $ addressTranslateS1 (VPtr pc)
              return $ pc' .|. (VPtr pc .&. mask pageBits)
          else
              return $ VPtr pc
    -- 32 is the width of the FSR field in the C VMFault structure:
    throw $ ArchFault $ VMFault pc [1, fault .&. mask 32]


{- Cache and TLB consistency -}

invalidateTLBByASID :: ASID -> Kernel ()
invalidateTLBByASID asid = do
    -- FIXME AARCH64: add SMMU
    maybeVMID <- loadHWASID asid
    when (isJust maybeVMID) $
        doMachineOp $ invalidateTranslationASID $ fromIntegral $ fromJust maybeVMID

doFlush :: FlushType -> VPtr -> VPtr -> PAddr -> MachineMonad ()
doFlush flushType vstart vend pstart =
    -- the address calculations that happen here on ARM_HYP are at the caller side in AARCH64
    case flushType of
        Clean           -> cleanCacheRange_RAM vstart vend pstart
        Invalidate      -> invalidateCacheRange_RAM vstart vend pstart
        CleanInvalidate -> cleanInvalidateCacheRange_RAM vstart vend pstart
        Unify           -> do
                               cleanCacheRange_PoU vstart vend pstart
                               dsb
                               invalidateCacheRange_I vstart vend pstart
                               branchFlushRange vstart vend pstart
                               isb

{- Unmapping and Deletion -}

-- When a capability backing a virtual memory mapping is deleted, or when an
-- explicit request is made to remove a mapping, the kernel must locate the
-- corresponding entries in the page table or ASID table and remove them. It is
-- also necessary to flush the removed mappings from the hardware caches.

{- Deleting an ASID Pool -}

deleteASIDPool :: ASID -> PPtr ASIDPool -> Kernel ()
deleteASIDPool base ptr = do
    assert (base .&. mask asidLowBits == 0)
        "ASID pool's base must be aligned"
    asidTable <- gets (armKSASIDTable . ksArchState)
    when (asidTable ! (asidHighBitsOf base) == Just ptr) $ do
        ASIDPool pool <- getObject ptr
        forM [0 .. bit asidLowBits - 1] $ \offset -> do
            when (isJust $ pool ! offset) $ do
                invalidateTLBByASID $ base + offset
                invalidateASIDEntry $ base + offset
        let asidTable' = asidTable//[(asidHighBitsOf base, Nothing)]
        modify (\s -> s {
            ksArchState = (ksArchState s) { armKSASIDTable = asidTable' }})
        tcb <- getCurThread
        setVMRoot tcb

{- Deleting an Address Space -}

deleteASID :: ASID -> PPtr PTE -> Kernel ()
deleteASID asid pt = do
    maybePoolPtr <- getPoolPtr asid
    case maybePoolPtr of
        Nothing -> return ()
        Just poolPtr -> do
            ASIDPool pool <- getObject poolPtr
            let maybeEntry = pool!(asid .&. mask asidLowBits)
            let maybeRoot = case maybeEntry of -- FIXME AARCH64: surely there is option.map
                 Just (ASIDPoolVSpace vmID p) -> Just p
                 Nothing -> Nothing
            when (maybeRoot == Just pt) $ do
                invalidateTLBByASID asid
                invalidateASIDEntry asid
                let pool' = pool//[(asid .&. mask asidLowBits, Nothing)]
                setObject poolPtr $ ASIDPool pool'
                tcb <- getCurThread
                setVMRoot tcb

{- Deleting a Page Table -}

-- Difference to lookupPTSlotFromLevel is that we are given a target page table
-- the slot should be in. If we don't find that page table during the walk, we
-- will throw an exception which is later ignored, in the sense that it is used
-- for early return + do nothing.
-- Returns only slots with pageTablePTEs
lookupPTFromLevel :: Int -> PPtr PTE -> VPtr -> PPtr PTE -> KernelF LookupFailure (PPtr PTE)
lookupPTFromLevel level ptPtr vPtr targetPtPtr = do
    assert (ptPtr /= targetPtPtr) "never called at top-level"
    unless (0 < level) $ throw InvalidRoot
    let slot = ptSlotIndex level ptPtr vPtr
    pte <- withoutFailure $ getObject slot
    unless (isPageTablePTE pte) $ throw InvalidRoot
    let ptr = getPPtrFromHWPTE pte
    if ptr == targetPtPtr
        then return slot
        else do
            withoutFailure $ checkPTAt ptr
            lookupPTFromLevel (level-1) ptr vPtr targetPtPtr

unmapPageTable :: ASID -> VPtr -> PPtr PTE -> Kernel ()
unmapPageTable asid vaddr pt = ignoreFailure $ do
    topLevelPT <- findVSpaceForASID asid
    ptSlot <- lookupPTFromLevel maxPTLevel topLevelPT vaddr pt
    withoutFailure $ storePTE ptSlot InvalidPTE
    withoutFailure $ doMachineOp sfence

{- Unmapping a Frame -}

-- If the previous PTE is not a page pointing at the same address we are
-- trying to unmap, the information is outdated and the operation should be ignored.
checkMappingPPtr :: PPtr Word -> PTE -> KernelF LookupFailure ()
checkMappingPPtr pptr pte =
    case pte of
        PagePTE { ptePPN = ppn } ->
            -- PagePTEs can only occur on non-toplevel tables
            unless (ptrFromPAddr (ppn `shiftL` ptBits False) == pptr) $ throw InvalidRoot
        _ -> throw InvalidRoot

unmapPage :: VMPageSize -> ASID -> VPtr -> PPtr Word -> Kernel ()
unmapPage size asid vptr pptr = ignoreFailure $ do
    vspace <- findVSpaceForASID asid
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    unless (bitsLeft == pageBitsForSize size) $ throw InvalidRoot
    pte <- withoutFailure $ getObject slot
    checkMappingPPtr pptr pte
    withoutFailure $ storePTE slot InvalidPTE
    withoutFailure $ doMachineOp sfence

{- Address Space Switching -}

setVMRoot :: PPtr TCB -> Kernel ()
setVMRoot tcb = do
    threadRootSlot <- getThreadVSpaceRoot tcb
    threadRoot <- getSlotCap threadRootSlot
    {- We use this in C to remove the check for isMapped: -}
    assert (isValidVTableRoot threadRoot || threadRoot == NullCap)
           "threadRoot must be valid or Null"
    catchFailure
        (case threadRoot of
            ArchObjectCap (PageTableCap {
                    capPTMappedAddress = Just (asid, _),
                    capPTBasePtr = pt }) -> do
                pt' <- findVSpaceForASID asid
                when (pt /= pt') $ throw InvalidRoot
                withoutFailure $ doMachineOp $
                    setVSpaceRoot (addrFromPPtr pt) (fromASID asid)
            _ -> throw InvalidRoot)
        (\_ -> do
            globalUserVSpace <- gets (armKSGlobalUserVSpace . ksArchState)
            doMachineOp $ setVSpaceRoot (addrFromKPPtr globalUserVSpace) 0)

-- FIXME AARCH64: based on ARM_HYP

{- Hardware ASID allocation -}

-- FIXME AARCH64: the naming here needs cleanup (in the C code as well) -- there
-- are no actual hardware ASIDs in EL-2, but VM IDs instead. Currently keeping
-- this so we can figure out what corresponds in C.

-- FIXME AARCH64: naming
storeHWASID :: ASID -> VMID -> Kernel ()
storeHWASID asid hw_asid = do
    updateASIDPoolEntry (\entry -> Just $ entry { apVMID = Just hw_asid }) asid
    hwASIDTable <- gets (armKSHWASIDTable . ksArchState)
    let hwASIDTable' = hwASIDTable//[(hw_asid, Just asid)]
    modify (\s -> s {
        ksArchState = (ksArchState s)
        { armKSHWASIDTable = hwASIDTable' }})

-- FIXME AARCH64: naming
-- FIXME AARCH64: the C PR removes this function, but it is still useful in
-- Haskell; it's mostly type wrangling and assertion so maybe not necessary for C
loadHWASID :: ASID -> Kernel (Maybe VMID)
loadHWASID asid = do
    maybeEntry <- getASIDPoolEntry asid
    case maybeEntry of
        Just (ASIDPoolVSpace vmID ptr) -> return vmID
        _ -> error ("loadHWASID: no entry for asid")

-- FIXME AARCH64: naming
invalidateASID :: ASID -> Kernel ()
invalidateASID = updateASIDPoolEntry (\entry -> Just $ entry { apVMID = Nothing })

-- FIXME AARCH64: naming
invalidateHWASIDEntry :: VMID -> Kernel ()
invalidateHWASIDEntry hwASID = do
    asidTable <- gets (armKSHWASIDTable . ksArchState)
    let asidTable' = asidTable//[(hwASID, Nothing)]
    modify (\s -> s {
        ksArchState = (ksArchState s)
        { armKSHWASIDTable = asidTable' }})

-- FIXME AARCH64: naming
invalidateASIDEntry :: ASID -> Kernel ()
invalidateASIDEntry asid = do
    maybeHWASID <- loadHWASID asid
    when (isJust maybeHWASID) $ invalidateHWASIDEntry (fromJust maybeHWASID)
    invalidateASID asid

-- FIXME AARCH64: update; currently verbatim from ARM
findFreeHWASID :: Kernel VMID
findFreeHWASID = do
    -- Look for a free Hardware ASID.
    hwASIDTable <- gets (armKSHWASIDTable . ksArchState)
    nextASID <- gets (armKSNextASID . ksArchState)
    let maybe_asid = find (\a -> isNothing (hwASIDTable ! a))
                    ([nextASID .. maxBound] ++ init [minBound .. nextASID])

    -- If there is one, return it, otherwise revoke the next one in a strict round-robin.
    case maybe_asid of
        Just hw_asid -> return hw_asid
        Nothing -> do
            invalidateASID $ fromJust $ hwASIDTable ! nextASID
            -- FIXME AARCH64: ARM had "doMachineOp $ invalidateLocalTLB_ASID nextASID"
            invalidateHWASIDEntry nextASID
            let new_nextASID =
                    if nextASID == maxBound
                    then minBound
                    else nextASID + 1
            modify (\s -> s {
                ksArchState = (ksArchState s)
                { armKSNextASID = new_nextASID }})
            return nextASID

-- FIXME AARCH64: naming
getHWASID :: ASID -> Kernel VMID
getHWASID asid = do
    maybe_hw_asid <- loadHWASID asid
    case maybe_hw_asid of
        Just hw_asid ->
            return hw_asid
        Nothing -> do
            new_hw_asid <- findFreeHWASID
            storeHWASID asid new_hw_asid
            return new_hw_asid

{- Helper Functions -}

isVTableRoot :: Capability -> Bool
isVTableRoot (ArchObjectCap (PageTableCap { capPTTopLevel = True })) = True
isVTableRoot _ = False

-- FIXME AARCH64: name indirection kept here for sync with C; both (C and
-- Haskell) should define isValidVTableRoot directly
isValidNativeRoot :: Capability -> Bool
isValidNativeRoot cap = isValidVTableRoot cap && isJust (capPTMappedAddress (capCap cap))

isValidVTableRoot :: Capability -> Bool
isValidVTableRoot = isValidNativeRoot

checkValidIPCBuffer :: VPtr -> Capability -> KernelF SyscallError ()
checkValidIPCBuffer vptr (ArchObjectCap (FrameCap {capFIsDevice = False})) = do
    when (vptr .&. mask ipcBufferSizeBits /= 0) $ throw AlignmentError
    return ()
checkValidIPCBuffer _ _ = throw IllegalOperation

maskVMRights :: VMRights -> CapRights -> VMRights
maskVMRights r m = case (r, capAllowRead m, capAllowWrite m) of
    (VMReadOnly, True, _) -> VMReadOnly
    (VMReadWrite, True, False) -> VMReadOnly
    (VMReadWrite, True, True) -> VMReadWrite
    _ -> VMKernelOnly


{- Decoding RISC-V Invocations -}

attribsFromWord :: Word -> VMAttributes
attribsFromWord w = VMAttributes { riscvExecuteNever = w `testBit` 0 }

makeUserPTE :: PAddr -> Bool -> VMRights -> PTE
makeUserPTE baseAddr executable rights =
    if rights == VMKernelOnly && not executable
    then InvalidPTE
    else PagePTE {
             ptePPN = baseAddr `shiftR` pageBits,
             pteGlobal = False,
             pteUser = True,
             pteExecute = executable,
             pteRights = rights }

checkVPAlignment :: VMPageSize -> VPtr -> KernelF SyscallError ()
checkVPAlignment sz w =
    unless (w .&. mask (pageBitsForSize sz) == 0) $ throw AlignmentError

checkSlot :: PPtr PTE -> (PTE -> Bool) -> KernelF SyscallError ()
checkSlot slot test = do
    pte <- withoutFailure $ getObject slot
    unless (test pte) $ throw DeleteFirst

labelToFlushType :: Word -> FlushType
labelToFlushType label = case invocationType label of
      ArchInvocationLabel ARMVSpaceClean_Data -> Clean
      ArchInvocationLabel ARMPageClean_Data -> Clean
      ArchInvocationLabel ARMVSpaceInvalidate_Data -> Invalidate
      ArchInvocationLabel ARMPageInvalidate_Data -> Invalidate
      ArchInvocationLabel ARMVSpaceCleanInvalidate_Data -> CleanInvalidate
      ArchInvocationLabel ARMPageCleanInvalidate_Data -> CleanInvalidate
      ArchInvocationLabel ARMVSpaceUnify_Instruction -> Unify
      ArchInvocationLabel ARMPageUnify_Instruction -> Unify
      _ -> error "Should never be called without a flush invocation"

pageBase :: (Num a, Bits a) => a -> Int -> a
pageBase vaddr size = vaddr .&. (complement $ mask size)

-- proof assertion only
checkValidMappingSize :: Int -> Kernel ()
checkValidMappingSize _ = return ()

decodeRISCVFrameInvocationMap :: PPtr CTE -> ArchCapability -> VPtr -> Word ->
    Word -> Capability -> KernelF SyscallError ArchInv.Invocation
decodeRISCVFrameInvocationMap cte cap vptr rightsMask attr vspaceCap = do
    (vspace,asid) <- case vspaceCap of
        ArchObjectCap (PageTableCap {
                capPTMappedAddress = Just (asid, _),
                capPTBasePtr = vspace })
            -> return (vspace, asid)
        _ -> throw $ InvalidCapability 1
    vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
    when (vspaceCheck /= vspace) $ throw $ InvalidCapability 1
    let pgBits = pageBitsForSize $ capFSize cap
    let vtop = vptr + (bit pgBits - 1)
    when (vtop >= pptrUserTop) $ throw $ InvalidArgument 0
    checkVPAlignment (capFSize cap) vptr
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    unless (bitsLeft == pgBits) $ throw $
        FailedLookup False $ MissingCapability bitsLeft
    case capFMappedAddress cap of
        Just (asid', vaddr') -> do
            when (asid' /= asid) $ throw $ InvalidCapability 1
            when (vaddr' /= vptr) $ throw $ InvalidArgument 0
            checkSlot slot (not . isPageTablePTE)
        Nothing -> checkSlot slot (\pte ->  pte == InvalidPTE)
    let vmRights = maskVMRights (capFVMRights cap) $ rightsFromWord rightsMask
    let framePAddr = addrFromPPtr (capFBasePtr cap)
    let exec = not $ riscvExecuteNever (attribsFromWord attr)
    return $ InvokePage $ PageMap {
        pageMapCap = ArchObjectCap $ cap { capFMappedAddress = Just (asid,vptr) },
        pageMapCTSlot = cte,
        pageMapEntries = (makeUserPTE framePAddr exec vmRights, slot) }

decodeARMFrameInvocationFlush :: Word -> [Word] -> ArchCapability ->
                                 KernelF SyscallError ArchInv.Invocation
decodeARMFrameInvocationFlush label args cap = case (args, capFMappedAddress cap) of
    (start:end:_, Just (asid, vaddr)) -> do
        vspaceRoot <- lookupErrorOnFailure False $ findVSpaceForASID asid
        when (end <= start) $ throw $ InvalidArgument 1
        let pageSize = bit (pageBitsForSize (capFSize cap))
        let pageBase = addrFromPPtr $ capFBasePtr cap
        when (start >= pageSize || end > pageSize) $ throw $ InvalidArgument 0
        let pstart = pageBase + toPAddr start
        when (pstart < paddrBase || ((end - start) + fromPAddr pstart > fromPAddr paddrTop)) $
            throw IllegalOperation
        return $ InvokePage $ PageFlush {
              pageFlushType = labelToFlushType label,
              pageFlushStart = VPtr $ fromVPtr vaddr + start,
              pageFlushEnd = VPtr $ fromVPtr vaddr + end - 1,
              pageFlushPStart = pstart,
              pageFlushSpace = vspaceRoot,
              pageFlushASID = asid }
    (_:_:_, Nothing) -> throw IllegalOperation
    _ -> throw TruncatedMessage

decodeARMFrameInvocation :: Word -> [Word] -> PPtr CTE ->
                            ArchCapability -> [(Capability, PPtr CTE)] ->
                            KernelF SyscallError ArchInv.Invocation
decodeARMFrameInvocation label args cte (cap@FrameCap {}) extraCaps =
    case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel ARMPageMap, vaddr:rightsMask:attr:_, (vspaceCap,_):_) -> do
            decodeRISCVFrameInvocationMap cte cap (VPtr vaddr) rightsMask attr vspaceCap
        (ArchInvocationLabel ARMPageMap, _, _) -> throw TruncatedMessage
        (ArchInvocationLabel ARMPageUnmap, _, _) ->
            return $ InvokePage $ PageUnmap {
                pageUnmapCap = cap,
                pageUnmapCapSlot = cte }
        (ArchInvocationLabel ARMPageGetAddress, _, _) ->
            return $ InvokePage $ PageGetAddr (capFBasePtr cap)
        (ArchInvocationLabel ARMPageClean_Data, _, _) ->
            decodeARMFrameInvocationFlush label args cap
        (ArchInvocationLabel ARMPageInvalidate_Data, _, _) ->
            decodeARMFrameInvocationFlush label args cap
        (ArchInvocationLabel ARMPageCleanInvalidate_Data, _, _) ->
            decodeARMFrameInvocationFlush label args cap
        (ArchInvocationLabel ARMPageUnify_Instruction, _, _) ->
            decodeARMFrameInvocationFlush label args cap
        _ -> throw IllegalOperation
decodeARMFrameInvocation _ _ _ _ _ = fail "Unreachable"


decodeRISCVPageTableInvocationMap :: PPtr CTE -> ArchCapability -> VPtr ->
    Word -> Capability -> KernelF SyscallError ArchInv.Invocation
decodeRISCVPageTableInvocationMap cte cap vptr attr vspaceCap = do
    when (isJust $ capPTMappedAddress cap) $ throw $ InvalidCapability 0
    (vspace,asid) <- case vspaceCap of
        ArchObjectCap (PageTableCap {
                 capPTMappedAddress = Just (asid,_),
                 capPTBasePtr = vspace })
            -> return (vspace,asid)
        _ -> throw $ InvalidCapability 1
    when (vptr >= pptrUserTop) $ throw $ InvalidArgument 0
    vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
    when (vspaceCheck /= vspace) $ throw $ InvalidCapability 1
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    oldPTE <- withoutFailure $ getObject slot
    when (bitsLeft == pageBits || oldPTE /= InvalidPTE) $ throw DeleteFirst
    let pte = PageTablePTE {
            ptePPN = addrFromPPtr (capPTBasePtr cap) `shiftR` pageBits,
            pteGlobal = False,
            pteUser = False }
    let vptr = vptr .&. complement (mask bitsLeft)
    return $ InvokePageTable $ PageTableMap {
        ptMapCap = ArchObjectCap $ cap { capPTMappedAddress = Just (asid, vptr) },
        ptMapCTSlot = cte,
        ptMapPTE = pte,
        ptMapPTSlot = slot }

decodeRISCVPageTableInvocation :: Word -> [Word] -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeRISCVPageTableInvocation label args cte cap@(PageTableCap {}) extraCaps =
   case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel ARMPageTableMap, vaddr:attr:_, (vspaceCap,_):_) -> do
            decodeRISCVPageTableInvocationMap cte cap (VPtr vaddr) attr vspaceCap
        (ArchInvocationLabel ARMPageTableMap, _, _) -> throw TruncatedMessage
        (ArchInvocationLabel ARMPageTableUnmap, _, _) -> do
            cteVal <- withoutFailure $ getCTE cte
            final <- withoutFailure $ isFinalCapability cteVal
            unless final $ throw RevokeFirst
            case cap of
                PageTableCap { capPTMappedAddress = Just (asid,_),
                               capPTBasePtr = pt }
                    -> do
                        -- top-level PTs must be unmapped via Revoke
                        maybeVSpace <- withoutFailure $ maybeVSpaceForASID asid
                        when (maybeVSpace == Just pt) $ throw RevokeFirst
                _ -> return ()
            return $ InvokePageTable $ PageTableUnmap {
                ptUnmapCap = cap,
                ptUnmapCapSlot = cte }
        _ -> throw IllegalOperation
decodeRISCVPageTableInvocation _ _ _ _ _ = fail "Unreachable"


decodeARMVSpaceRootInvocation :: Word -> [Word] -> ArchCapability ->
        KernelF SyscallError ArchInv.Invocation
decodeARMVSpaceRootInvocation label args cap@(PageTableCap { capPTTopLevel = True }) =
    case (isVSpaceFlushLabel (invocationType label), args) of
        (True, start:end:_) -> do
            when (end <= start) $ throw $ InvalidArgument 1
            when (VPtr end > pptrUserTop) $ throw IllegalOperation
            -- equivalent to isValidNativeRoot:
            (vspaceRoot, asid) <- case cap of
                PageTableCap {
                         capPTMappedAddress = Just (asid, _),
                         capPTBasePtr = pt}
                    -> return (pt, asid)
                _ -> throw $ InvalidCapability 0
            ptCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
            when (ptCheck /= vspaceRoot) $ throw $ InvalidCapability 0
            frameInfo <- withoutFailure $ lookupFrame (capPTBasePtr cap) (VPtr start)
            case frameInfo of
                -- Ignore call if there is nothing mapped here
                Nothing -> return $ InvokeVSpaceRoot VSpaceRootNothing
                Just frameInfo -> do
                    withoutFailure $ checkValidMappingSize (fst frameInfo)
                    let baseStart = pageBase (VPtr start) (fst frameInfo)
                    let baseEnd = pageBase (VPtr end - 1) (fst frameInfo)
                    when (baseStart /= baseEnd) $
                        throw $ RangeError start $ fromVPtr $ baseStart + mask (fst frameInfo)
                    let offset = start .&. mask (fst frameInfo)
                    let pStart = snd frameInfo + toPAddr offset
                    return $ InvokeVSpaceRoot $ VSpaceRootFlush {
                         vsFlushType = labelToFlushType label,
                         vsFlushStart = VPtr start,
                         vsFlushEnd = VPtr end - 1,
                         vsFlushPStart = pStart,
                         vsFlushSpace = vspaceRoot,
                         vsFlushASID = asid }
        (True, _) -> throw TruncatedMessage
        _ -> throw IllegalOperation
decodeARMVSpaceRootInvocation _ _ _ = fail "Unreachable"


decodeRISCVASIDControlInvocation :: Word -> [Word] ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation

decodeRISCVASIDControlInvocation label args ASIDControlCap extraCaps =
    case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel ARMASIDControlMakePool, index:depth:_,
                        (untyped,parentSlot):(croot,_):_) -> do
            asidTable <- withoutFailure $ gets (armKSASIDTable . ksArchState)
            let free = filter (\(x,y) -> x <= (1 `shiftL` asidHighBits) - 1 && isNothing y) $ assocs asidTable
            when (null free) $ throw DeleteFirst
            let base = (fst $ head free) `shiftL` asidLowBits
            let pool = makeObject :: ASIDPool
            frame <- case untyped of
                UntypedCap { capIsDevice = False } | capBlockSize untyped == objBits pool -> do
                    ensureNoChildren parentSlot
                    return $ capPtr untyped
                _ -> throw $ InvalidCapability 1
            destSlot <- lookupTargetSlot croot (CPtr index) (fromIntegral depth)
            ensureEmptySlot destSlot
            return $ InvokeASIDControl $ MakePool {
                makePoolFrame = frame,
                makePoolSlot = destSlot,
                makePoolParent = parentSlot,
                makePoolBase = base }
        (ArchInvocationLabel ARMASIDControlMakePool, _, _) -> throw TruncatedMessage
        _ -> throw IllegalOperation
decodeRISCVASIDControlInvocation _ _ _ _ = fail "Unreachable"


decodeRISCVASIDPoolInvocation :: Word ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation

decodeRISCVASIDPoolInvocation label cap@(ASIDPoolCap {}) extraCaps =
    case (invocationType label, extraCaps) of
        (ArchInvocationLabel ARMASIDPoolAssign, (vspaceCap,vspaceCapSlot):_) ->
            case vspaceCap of
                ArchObjectCap (PageTableCap { capPTMappedAddress = Nothing })
                  -> do
                    asidTable <- withoutFailure $ gets (armKSASIDTable . ksArchState)
                    let base = capASIDBase cap
                    let poolPtr = asidTable!(asidHighBitsOf base)
                    when (isNothing poolPtr) $ throw $ FailedLookup False InvalidRoot
                    let Just p = poolPtr
                    when (p /= capASIDPool cap) $ throw $ InvalidCapability 0
                    ASIDPool pool <- withoutFailure $ getObject $ p
                    let free = filter (\(x,y) -> x <=  (1 `shiftL` asidLowBits) - 1
                                                 && x + base /= 0 && isNothing y) $ assocs pool
                    when (null free) $ throw DeleteFirst
                    let asid = fst $ head free
                    return $ InvokeASIDPool $ Assign {
                        assignASID = asid + base,
                        assignASIDPool = capASIDPool cap,
                        assignASIDCTSlot = vspaceCapSlot }
                _ -> throw $ InvalidCapability 1
        (ArchInvocationLabel ARMASIDPoolAssign, _) -> throw TruncatedMessage
        _ -> throw IllegalOperation
decodeRISCVASIDPoolInvocation _ _ _ = fail "Unreachable"


decodeARMMMUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeARMMMUInvocation label args _ cte cap@(FrameCap {}) extraCaps =
    decodeARMFrameInvocation label args cte cap extraCaps
decodeARMMMUInvocation label args _ cte cap@(PageTableCap { capPTTopLevel = False }) extraCaps =
    decodeRISCVPageTableInvocation label args cte cap extraCaps
decodeARMMMUInvocation label args _ cte cap@(PageTableCap { capPTTopLevel = True }) extraCaps =
    decodeARMVSpaceRootInvocation label args cap
decodeARMMMUInvocation label args _ _ cap@(ASIDControlCap {}) extraCaps =
    decodeRISCVASIDControlInvocation label args cap extraCaps
decodeARMMMUInvocation label _ _ _ cap@(ASIDPoolCap {}) extraCaps =
    decodeRISCVASIDPoolInvocation label cap extraCaps
decodeARMMMUInvocation _ _ _ _ (VCPUCap {}) _ = fail "decodeARMMMUInvocation: not an MMU invocation"


{- Invocation Implementations -}

performVSpaceRootInvocation :: VSpaceRootInvocation -> Kernel ()
performVSpaceRootInvocation VSpaceRootNothing = return ()
performVSpaceRootInvocation (VSpaceRootFlush flushType vstart vend pstart space asid) = do
    let start = VPtr $ fromPPtr $ ptrFromPAddr pstart
    let end = start + (vend - vstart)
    when (start < end) $ do
        doMachineOp $ doFlush flushType start end pstart


performPageTableInvocation :: PageTableInvocation -> Kernel ()
performPageTableInvocation (PageTableMap cap ctSlot pte ptSlot) = do
    updateCap ctSlot cap
    storePTE ptSlot pte
    doMachineOp sfence

performPageTableInvocation (PageTableUnmap cap slot) = do
    case capPTMappedAddress cap of
        Just (asid, vaddr) -> do
            let ptr = capPTBasePtr cap
            unmapPageTable asid vaddr ptr
            let slots = [ptr, ptr + bit pteBits .. ptr + bit (ptBits (capPTTopLevel cap)) - 1]
            mapM_ (flip storePTE InvalidPTE) slots
        _ -> return ()
    ArchObjectCap cap <- getSlotCap slot
    updateCap slot (ArchObjectCap $ cap { capPTMappedAddress = Nothing })


performPageInvocation :: PageInvocation -> Kernel ()
performPageInvocation (PageMap cap ctSlot (pte,slot)) = do
    updateCap ctSlot cap
    storePTE slot pte
    doMachineOp sfence

performPageInvocation (PageUnmap cap ctSlot) = do
    case capFMappedAddress cap of
        Just (asid, vaddr) -> unmapPage (capFSize cap) asid vaddr (capFBasePtr cap)
        _ -> return ()
    ArchObjectCap cap <- getSlotCap ctSlot
    updateCap ctSlot (ArchObjectCap $ cap { capFMappedAddress = Nothing })

performPageInvocation (PageGetAddr ptr) = do
    let paddr = fromPAddr $ addrFromPPtr ptr
    ct <- getCurThread
    msgTransferred <- setMRs ct Nothing [paddr]
    msgInfo <- return $ MI {
            msgLength = msgTransferred,
            msgExtraCaps = 0,
            msgCapsUnwrapped = 0,
            msgLabel = 0 }
    setMessageInfo ct msgInfo

performPageInvocation (PageFlush flushType vstart vend pstart space asid) = do
    let start = VPtr $ fromPPtr $ ptrFromPAddr pstart
    let end = start + (vend - vstart)
    when (start < end) $ do
        doMachineOp $ doFlush flushType start end pstart


performASIDControlInvocation :: ASIDControlInvocation -> Kernel ()
performASIDControlInvocation (MakePool frame slot parent base) = do
    deleteObjects frame pageBits
    pcap <- getSlotCap parent
    updateFreeIndex parent (maxFreeIndex (capBlockSize pcap))
    placeNewObject frame (makeObject :: ASIDPool) 0
    let poolPtr = PPtr $ fromPPtr frame
    cteInsert (ArchObjectCap $ ASIDPoolCap poolPtr base) parent slot
    assert (base .&. mask asidLowBits == 0)
        "ASID pool's base must be aligned"
    asidTable <- gets (armKSASIDTable . ksArchState)
    let asidTable' = asidTable//[(asidHighBitsOf base, Just poolPtr)]
    modify (\s -> s {
        ksArchState = (ksArchState s) { armKSASIDTable = asidTable' }})


performASIDPoolInvocation :: ASIDPoolInvocation -> Kernel ()
performASIDPoolInvocation (Assign asid poolPtr ctSlot) = do
    oldcap <- getSlotCap ctSlot
    let ArchObjectCap cap = oldcap
    updateCap ctSlot (ArchObjectCap $ cap { capPTMappedAddress = Just (asid,0) })
    ASIDPool pool <- getObject poolPtr
    let pool' = pool//[(asid .&. mask asidLowBits,
                        Just $ ASIDPoolVSpace Nothing $ capPTBasePtr cap)]
    setObject poolPtr $ ASIDPool pool'

performARMMMUInvocation :: ArchInv.Invocation -> KernelP [Word]
performARMMMUInvocation i = withoutPreemption $ do
    case i of
        InvokeVSpaceRoot oper -> performVSpaceRootInvocation oper
        InvokePageTable oper -> performPageTableInvocation oper
        InvokePage oper -> performPageInvocation oper
        InvokeASIDControl oper -> performASIDControlInvocation oper
        InvokeASIDPool oper -> performASIDPoolInvocation oper
        InvokeVCPU _ -> fail "performARMMMUInvocation: not an MMU invocation"
    return $ []

storePTE :: PPtr PTE -> PTE -> Kernel ()
storePTE slot pte = do
    setObject slot pte

{- Unimplemented Boot Code Stubs -}

mapKernelWindow  :: Kernel ()
mapKernelWindow = error "boot code unimplemented"

activateGlobalVSpace :: Kernel ()
activateGlobalVSpace = error "boot code unimplemented"

createIPCBufferFrame :: Capability -> VPtr -> KernelInit Capability
createIPCBufferFrame = error "boot code unimplemented"

createBIFrame :: Capability -> VPtr -> Word32 -> Word32 -> KernelInit Capability
createBIFrame = error "boot code unimplemented"

createFramesOfRegion :: Capability -> Region -> Bool -> KernelInit ()
createFramesOfRegion = error "boot code unimplemented"

createITPDPTs :: Capability -> VPtr -> VPtr -> KernelInit Capability
createITPDPTs  = error "boot code unimplemented"

writeITPDPTs :: Capability -> Capability -> KernelInit ()
writeITPDPTs  = error "boot code unimplemented"

createITASIDPool :: Capability -> KernelInit Capability
createITASIDPool  = error "boot code unimplemented"

writeITASIDPool :: Capability -> Capability -> Kernel ()
writeITASIDPool  = error "boot code unimplemented"

createDeviceFrames :: Capability -> KernelInit ()
createDeviceFrames  = error "boot code unimplemented"

vptrFromPPtr :: PPtr a -> KernelInit VPtr
vptrFromPPtr  = error "boot code unimplemented"
