--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the handling of the AARCH64 hardware-defined page tables.

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
import Data.WordLib

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

-- FIXME: make this a Reader Monad when we move to MCS
getPoolPtr :: ASID -> Kernel (Maybe (PPtr ASIDPool))
getPoolPtr asid = do
    assert (asid > 0) "ASID 0 is used for objects that are not mapped"
    assert (asid <= snd asidRange) "ASID out of range"
    asidTable <- gets (armKSASIDTable . ksArchState)
    return $ asidTable!(asidHighBitsOf asid)

-- FIXME: make this a Reader Monad when we move to MCS
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

getPPtrFromPTE :: PTE -> PPtr PTE
getPPtrFromPTE pte =
    ptrFromPAddr (if isPagePTE pte then pteBaseAddress pte else ptePPN pte `shiftL` pageBits)

-- how many bits there are left to be translated at a given level (0 = bottom
-- level). This counts the bits being translated by the levels below the current one, so
-- no case distinction needed for maxPTLevel and below. We include the separate case for the
-- ASID pool level, because this function is also used in invariants.
-- Example for maxPTLevel: if maxPTLevel = 2, and we are on level 2, that means level 0 and 1
-- are below us and we still need translate the bits for level 0 and 1 after
-- this lookup, but not the ones from level 2, so only level 0 and 1 (= 2 levels) need to be
-- counted in ptBitsLeft.
ptBitsLeft :: Int -> Int
ptBitsLeft level =
  (if level <= maxPTLevel
   then ptTranslationBits NormalPT_T * level
   else ptTranslationBits VSRootPT_T + ptTranslationBits NormalPT_T * maxPTLevel) + pageBits

levelType :: Int -> PT_Type
levelType level = if level == maxPTLevel then VSRootPT_T else NormalPT_T

-- compute index into a page table from vPtr at given level
ptIndex :: Int -> VPtr -> Word
ptIndex level vPtr =
    (fromVPtr vPtr `shiftR` ptBitsLeft level) .&. mask (ptTranslationBits (levelType level))

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
            checkPTAt (getPPtrFromPTE pte)
            lookupPTSlotFromLevel (level-1) (getPPtrFromPTE pte) vPtr
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
        then return $ Just (bitsLeft, pteBaseAddress pte)
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
                -- address bits of PAR register after S1 translation
                let parEL1Mask = 0xfffffffff000
                addr' <- withoutFailure $ doMachineOp $ addressTranslateS1 addr
                return $ (addr' .&. parEL1Mask) .|. (addr .&. mask pageBits)
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
              -- address bits of PAR register after S1 translation
              let parEL1Mask = 0xfffffffff000
              pc' <- withoutFailure $ doMachineOp $ addressTranslateS1 (VPtr pc)
              return $ (pc' .&. parEL1Mask) .|. (VPtr pc .&. mask pageBits)
          else
              return $ VPtr pc
    -- 32 is the width of the FSR field in the C VMFault structure:
    throw $ ArchFault $ VMFault pc [1, fault .&. mask 32]


{- Cache and TLB consistency -}

invalidateTLBByASID :: ASID -> Kernel ()
invalidateTLBByASID asid = do
    -- TODO AARCH64: add SMMU
    maybeVMID <- loadVMID asid
    when (isJust maybeVMID) $
        doMachineOp $ invalidateTranslationASID $ fromIntegral $ fromJust maybeVMID

invalidateTLBByASIDVA :: ASID -> VPtr -> Kernel ()
invalidateTLBByASIDVA asid vaddr = do
    -- TODO AARCH64: add SMMU
    maybeVMID <- loadVMID asid
    when (isJust maybeVMID) $ do
        let vmID = fromJust maybeVMID
        let shift = wordBits - asidBits
        let vpn = fromIntegral vmID `shiftL` shift .|. fromVPtr vaddr `shiftR` pageBits
        doMachineOp $ invalidateTranslationSingle vpn

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
            let maybeRoot = maybe Nothing (Just . apVSpace) maybeEntry
            when (maybeRoot == Just pt) $ do
                invalidateTLBByASID asid
                invalidateASIDEntry asid
                -- re-read pool, because invalidateASIDEntry changes it
                ASIDPool pool <- getObject poolPtr
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
    let ptr = getPPtrFromPTE pte
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
    withoutFailure $ doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr ptSlot) (addrFromPPtr ptSlot)
    withoutFailure $ invalidateTLBByASID asid

{- Unmapping a Frame -}

-- If the previous PTE is not a page pointing at the same address we are
-- trying to unmap, the information is outdated and the operation should be ignored.
checkMappingPPtr :: PPtr Word -> PTE -> KernelF LookupFailure ()
checkMappingPPtr pptr pte =
    case pte of
        PagePTE { pteBaseAddress = addr } ->
            unless (addr == addrFromPPtr pptr) $ throw InvalidRoot
        _ -> throw InvalidRoot

unmapPage :: VMPageSize -> ASID -> VPtr -> PPtr Word -> Kernel ()
unmapPage size asid vptr pptr = ignoreFailure $ do
    vspace <- findVSpaceForASID asid
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    unless (bitsLeft == pageBitsForSize size) $ throw InvalidRoot
    pte <- withoutFailure $ getObject slot
    checkMappingPPtr pptr pte
    withoutFailure $ storePTE slot InvalidPTE
    withoutFailure $ doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr slot) (addrFromPPtr slot)
    withoutFailure $ invalidateTLBByASIDVA asid vptr

{- Address Space Switching -}

armContextSwitch :: PPtr PTE -> ASID -> Kernel ()
armContextSwitch vspace asid = do
    vmID <- getVMID asid
    doMachineOp $ setVSpaceRoot (addrFromPPtr vspace) (fromIntegral vmID)

setGlobalUserVSpace :: Kernel ()
setGlobalUserVSpace = do
    globalUserVSpace <- gets (armKSGlobalUserVSpace . ksArchState)
    doMachineOp $ setVSpaceRoot (addrFromKPPtr globalUserVSpace) 0

setVMRoot :: PPtr TCB -> Kernel ()
setVMRoot tcb = do
    threadRootSlot <- getThreadVSpaceRoot tcb
    threadRoot <- getSlotCap threadRootSlot
    {- This means C does not need to check for isMapped: -}
    assert (isValidVTableRoot threadRoot || threadRoot == NullCap)
           "threadRoot must be valid or Null"
    catchFailure
        (case threadRoot of
            ArchObjectCap (PageTableCap {
                    capPTType = VSRootPT_T,
                    capPTMappedAddress = Just (asid, _),
                    capPTBasePtr = vspaceRoot }) -> do
                vspaceRoot' <- findVSpaceForASID asid
                when (vspaceRoot /= vspaceRoot') $ throw InvalidRoot
                withoutFailure $ armContextSwitch vspaceRoot asid
            _ -> throw InvalidRoot)
        (\_ -> setGlobalUserVSpace)

{- Hardware ASID allocation -}

storeVMID :: ASID -> VMID -> Kernel ()
storeVMID asid vmid = do
    updateASIDPoolEntry (\entry -> Just $ entry { apVMID = Just vmid }) asid
    vmidTable <- gets (armKSVMIDTable . ksArchState)
    let vmidTable' = vmidTable//[(vmid, Just asid)]
    modify (\s -> s {
        ksArchState = (ksArchState s)
        { armKSVMIDTable = vmidTable' }})

-- This function is removed in C, but it is still useful in Haskell; it's
-- mostly type wrangling and assertion so maybe not necessary for C
loadVMID :: ASID -> Kernel (Maybe VMID)
loadVMID asid = do
    maybeEntry <- getASIDPoolEntry asid
    case maybeEntry of
        Just (ASIDPoolVSpace vmID ptr) -> return vmID
        _ -> fail "loadVMID: no entry for asid"

invalidateASID :: ASID -> Kernel ()
invalidateASID = updateASIDPoolEntry (\entry -> Just $ entry { apVMID = Nothing })

invalidateVMIDEntry :: VMID -> Kernel ()
invalidateVMIDEntry vmid = do
    vmidTable <- gets (armKSVMIDTable . ksArchState)
    let vmidTable' = vmidTable//[(vmid, Nothing)]
    modify (\s -> s {
        ksArchState = (ksArchState s)
        { armKSVMIDTable = vmidTable' }})

invalidateASIDEntry :: ASID -> Kernel ()
invalidateASIDEntry asid = do
    maybeVMID <- loadVMID asid
    when (isJust maybeVMID) $ invalidateVMIDEntry (fromJust maybeVMID)
    invalidateASID asid

findFreeVMID :: Kernel VMID
findFreeVMID = do
    -- Look for a free VM ID.
    vmidTable <- gets (armKSVMIDTable . ksArchState)
    nextVMID <- gets (armKSNextVMID . ksArchState)
    let maybeVMID = find (\a -> isNothing (vmidTable ! a))
                    ([nextVMID .. maxBound] ++ init [minBound .. nextVMID])

    -- If there is one, return it, otherwise revoke the next one in a strict round-robin.
    case maybeVMID of
        Just vmid -> return vmid
        Nothing -> do
            invalidateASID $ fromJust $ vmidTable ! nextVMID
            doMachineOp $ invalidateTranslationASID $ fromIntegral nextVMID
            invalidateVMIDEntry nextVMID
            let new_nextVMID = if nextVMID == maxBound then minBound else nextVMID + 1
            modify (\s -> s { ksArchState = (ksArchState s) { armKSNextVMID = new_nextVMID }})
            return nextVMID

getVMID :: ASID -> Kernel VMID
getVMID asid = do
    maybeVMID <- loadVMID asid
    case maybeVMID of
        Just vmid ->
            return vmid
        Nothing -> do
            newVMID <- findFreeVMID
            storeVMID asid newVMID
            return newVMID

{- Helper Functions -}

isVTableRoot :: Capability -> Bool
isVTableRoot (ArchObjectCap (PageTableCap { capPTType = VSRootPT_T })) = True
isVTableRoot _ = False

isValidVTableRoot :: Capability -> Bool
isValidVTableRoot cap = isVTableRoot cap && isJust (capPTMappedAddress (capCap cap))

-- if isValidVTableRoot holds, return VSpace and ASID, otherwise throw error
checkVSpaceRoot :: Capability  -> Int -> KernelF SyscallError (PPtr PTE, ASID)
checkVSpaceRoot vspaceCap argNo =
    case vspaceCap of
        ArchObjectCap (PageTableCap {
                capPTMappedAddress = Just (asid, _),
                capPTBasePtr = vspace })
            -> return (vspace, asid)
        _ -> throw $ InvalidCapability argNo

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


{- Decoding AARCH64 Invocations -}

attribsFromWord :: Word -> VMAttributes
attribsFromWord w = VMAttributes {
    armExecuteNever = w `testBit` 2,
    armPageCacheable = w `testBit` 0 }

makeUserPTE :: PAddr -> VMRights -> VMAttributes -> VMPageSize -> PTE
makeUserPTE baseAddr rights attrs vmSize =
    PagePTE {
        pteBaseAddress = baseAddr,
        pteSmallPage = vmSize == ARMSmallPage,
        pteGlobal = False,
        pteExecuteNever = armExecuteNever attrs,
        pteDevice = not (armPageCacheable attrs),
        pteRights = rights }

checkVPAlignment :: VMPageSize -> VPtr -> KernelF SyscallError ()
checkVPAlignment sz w =
    unless (w .&. mask (pageBitsForSize sz) == 0) $ throw AlignmentError

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

decodeARMFrameInvocationMap :: PPtr CTE -> ArchCapability -> VPtr -> Word ->
    Word -> Capability -> KernelF SyscallError ArchInv.Invocation
decodeARMFrameInvocationMap cte cap vptr rightsMask attr vspaceCap = do
    let attributes = attribsFromWord attr
    let frameSize = capFSize cap
    let vmRights = maskVMRights (capFVMRights cap) $ rightsFromWord rightsMask
    (vspace,asid) <- checkVSpaceRoot vspaceCap 1
    vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
    when (vspaceCheck /= vspace) $ throw $ InvalidCapability 1
    checkVPAlignment frameSize vptr
    let pgBits = pageBitsForSize frameSize
    case capFMappedAddress cap of
        Just (asid', vaddr') -> do
            when (asid' /= asid) $ throw $ InvalidCapability 1
            when (vaddr' /= vptr) $ throw $ InvalidArgument 0
        Nothing -> do
            let vtop = vptr + (bit pgBits - 1)
            when (vtop > pptrUserTop) $ throw $ InvalidArgument 0
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    unless (bitsLeft == pgBits) $ throw $ FailedLookup False $ MissingCapability bitsLeft
    let base = addrFromPPtr (capFBasePtr cap)
    return $ InvokePage $ PageMap {
        pageMapCap = cap { capFMappedAddress = Just (asid,vptr) },
        pageMapCTSlot = cte,
        pageMapEntries = (makeUserPTE base vmRights attributes frameSize, slot) }

decodeARMFrameInvocationFlush :: Word -> [Word] -> ArchCapability ->
                                 KernelF SyscallError ArchInv.Invocation
decodeARMFrameInvocationFlush label args cap = case (args, capFMappedAddress cap) of
    (start:end:_, Just (asid, vaddr)) -> do
        vspaceRoot <- lookupErrorOnFailure False $ findVSpaceForASID asid
        when (end <= start) $ throw $ InvalidArgument 1
        let pageSize = bit (pageBitsForSize (capFSize cap))
        when (start >= pageSize || end > pageSize) $ throw $ InvalidArgument 0
        let pageBase = addrFromPPtr $ capFBasePtr cap
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
            decodeARMFrameInvocationMap cte cap (VPtr vaddr) rightsMask attr vspaceCap
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


decodeARMPageTableInvocationMap :: PPtr CTE -> ArchCapability -> VPtr ->
    Word -> Capability -> KernelF SyscallError ArchInv.Invocation
decodeARMPageTableInvocationMap cte cap vptr attr vspaceCap = do
    when (isJust $ capPTMappedAddress cap) $ throw $ InvalidCapability 0
    (vspace,asid) <- checkVSpaceRoot vspaceCap 1
    when (vptr > pptrUserTop) $ throw $ InvalidArgument 0
    vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
    when (vspaceCheck /= vspace) $ throw $ InvalidCapability 1
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    oldPTE <- withoutFailure $ getObject slot
    when (bitsLeft == pageBits || oldPTE /= InvalidPTE) $ throw DeleteFirst
    let pte = PageTablePTE {
            ptePPN = addrFromPPtr (capPTBasePtr cap) `shiftR` pageBits }
    let vptr = vptr .&. complement (mask bitsLeft)
    return $ InvokePageTable $ PageTableMap {
        ptMapCap = ArchObjectCap $ cap { capPTMappedAddress = Just (asid, vptr) },
        ptMapCTSlot = cte,
        ptMapPTE = pte,
        ptMapPTSlot = slot }

decodeARMPageTableInvocation :: Word -> [Word] -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeARMPageTableInvocation label args cte cap@(PageTableCap {}) extraCaps =
   case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel ARMPageTableMap, vaddr:attr:_, (vspaceCap,_):_) -> do
            decodeARMPageTableInvocationMap cte cap (VPtr vaddr) attr vspaceCap
        (ArchInvocationLabel ARMPageTableMap, _, _) -> throw TruncatedMessage
        (ArchInvocationLabel ARMPageTableUnmap, _, _) -> do
            cteVal <- withoutFailure $ getCTE cte
            final <- withoutFailure $ isFinalCapability cteVal
            unless final $ throw RevokeFirst
            return $ InvokePageTable $ PageTableUnmap {
                ptUnmapCap = cap,
                ptUnmapCapSlot = cte }
        _ -> throw IllegalOperation
decodeARMPageTableInvocation _ _ _ _ _ = fail "Unreachable"


decodeARMVSpaceInvocation :: Word -> [Word] -> ArchCapability ->
        KernelF SyscallError ArchInv.Invocation
decodeARMVSpaceInvocation label args cap@(PageTableCap { capPTType = VSRootPT_T }) =
    case (isVSpaceFlushLabel (invocationType label), args) of
        (True, start:end:_) -> do
            when (end <= start) $ throw $ InvalidArgument 1
            when (VPtr end > pptrUserTop) $ throw IllegalOperation
            (vspaceRoot, asid) <- checkVSpaceRoot (ArchObjectCap cap) 0
            ptCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
            when (ptCheck /= vspaceRoot) $ throw $ InvalidCapability 0
            frameInfo <- withoutFailure $ lookupFrame (capPTBasePtr cap) (VPtr start)
            case frameInfo of
                -- Ignore call if there is nothing mapped here
                Nothing -> return $ InvokeVSpace VSpaceNothing
                Just (bitsLeft, pAddr) -> do
                    withoutFailure $ checkValidMappingSize bitsLeft
                    let baseStart = pageBase (VPtr start) bitsLeft
                    let baseEnd = pageBase (VPtr end - 1) bitsLeft
                    when (baseStart /= baseEnd) $
                        throw $ RangeError start $ fromVPtr $ baseStart + mask bitsLeft
                    let offset = start .&. mask bitsLeft
                    let pStart = pAddr + toPAddr offset
                    return $ InvokeVSpace $ VSpaceFlush {
                         vsFlushType = labelToFlushType label,
                         vsFlushStart = VPtr start,
                         vsFlushEnd = VPtr end - 1,
                         vsFlushPStart = pStart,
                         vsFlushSpace = vspaceRoot,
                         vsFlushASID = asid }
        (True, _) -> throw TruncatedMessage
        _ -> throw IllegalOperation
decodeARMVSpaceInvocation _ _ _ = fail "Unreachable"


decodeARMASIDControlInvocation :: Word -> [Word] ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeARMASIDControlInvocation label args ASIDControlCap extraCaps =
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
decodeARMASIDControlInvocation _ _ _ _ = fail "Unreachable"


decodeARMASIDPoolInvocation :: Word ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeARMASIDPoolInvocation label cap@(ASIDPoolCap {}) extraCaps =
    case (invocationType label, extraCaps) of
        (ArchInvocationLabel ARMASIDPoolAssign, (vspaceCap,vspaceCapSlot):_) ->
            case vspaceCap of
                ArchObjectCap (PageTableCap { capPTMappedAddress = Nothing })
                  -> do
                    -- C checks for a mapping here, but our case already checks that
                    when (not (isVTableRoot vspaceCap)) $
                        throw $ InvalidCapability 1
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
decodeARMASIDPoolInvocation _ _ _ = fail "Unreachable"


decodeARMMMUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeARMMMUInvocation label args _ cte cap@(FrameCap {}) extraCaps =
    decodeARMFrameInvocation label args cte cap extraCaps
decodeARMMMUInvocation label args _ cte cap@(PageTableCap { capPTType = NormalPT_T }) extraCaps =
    decodeARMPageTableInvocation label args cte cap extraCaps
decodeARMMMUInvocation label args _ cte cap@(PageTableCap { capPTType = VSRootPT_T }) extraCaps =
    decodeARMVSpaceInvocation label args cap
decodeARMMMUInvocation label args _ _ cap@(ASIDControlCap {}) extraCaps =
    decodeARMASIDControlInvocation label args cap extraCaps
decodeARMMMUInvocation label _ _ _ cap@(ASIDPoolCap {}) extraCaps =
    decodeARMASIDPoolInvocation label cap extraCaps
decodeARMMMUInvocation _ _ _ _ (VCPUCap {}) _ = fail "decodeARMMMUInvocation: not an MMU invocation"


{- Invocation Implementations -}

performVSpaceInvocation :: VSpaceInvocation -> Kernel ()
performVSpaceInvocation VSpaceNothing = return ()
performVSpaceInvocation (VSpaceFlush flushType vstart vend pstart space asid) = do
    let start = VPtr $ fromPPtr $ ptrFromPAddr pstart
    let end = start + (vend - vstart)
    when (start < end) $ do
        doMachineOp $ doFlush flushType start end pstart


performPageTableInvocation :: PageTableInvocation -> Kernel ()
performPageTableInvocation (PageTableMap cap ctSlot pte ptSlot) = do
    updateCap ctSlot cap
    storePTE ptSlot pte
    doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr ptSlot) (addrFromPPtr ptSlot)

performPageTableInvocation (PageTableUnmap cap slot) = do
    case capPTMappedAddress cap of
        Just (asid, vaddr) -> do
            let ptr = capPTBasePtr cap
            unmapPageTable asid vaddr ptr
            let slots = [ptr, ptr + bit pteBits .. ptr + bit (ptBits (capPTType cap)) - 1]
            mapM_ (flip storePTE InvalidPTE) slots
        _ -> return ()
    ArchObjectCap cap <- getSlotCap slot
    updateCap slot (ArchObjectCap $ cap { capPTMappedAddress = Nothing })


performPageInvocation :: PageInvocation -> Kernel ()
performPageInvocation (PageMap cap ctSlot (pte,slot)) = do
    oldPte <- getObject slot
    let tlbFlushRequired = oldPte /= InvalidPTE
    updateCap ctSlot (ArchObjectCap cap)
    storePTE slot pte
    doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr slot) (addrFromPPtr slot)
    when tlbFlushRequired $ do
        (asid, vaddr) <- return $ fromJust $ capFMappedAddress cap
        invalidateTLBByASIDVA asid vaddr

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
        InvokeVSpace oper -> performVSpaceInvocation oper
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
