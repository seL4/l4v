%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the handling of the ARM hardware-defined page tables.

FIXME ARMHYP this file is only for ARM\_HYP, uses preprocessor only to disable SMMU unlike nearly all the other ones; fixable, but too much clutter for the moment

FIXME ARMHYP the amount of magic numbers is staggering

\begin{impdetails}

FIXME ARMHYP this is so that disabling SMMU results in successful compile

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Kernel.VSpace.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Failures.ARM
> import SEL4.Machine.RegisterSet
> import SEL4.Machine.Hardware.ARM
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Model.StateData.ARM
> import SEL4.Object.Instances()
> import SEL4.API.InvocationLabels
> import SEL4.Kernel.BootInfo
> import {-# SOURCE #-} SEL4.Object.CNode
> import {-# SOURCE #-} SEL4.Object.TCB
> import {-# SOURCE #-} SEL4.Kernel.Init
> import {-# SOURCE #-} SEL4.Kernel.CSpace
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> import SEL4.Object.VCPU.ARM
#endif

> import Data.Bits
> import Data.Maybe
> import Data.List
> import Data.Array
> import Data.Word(Word32)
> import Data.WordLib

\end{impdetails}

The ARM-specific invocations are imported with the "ArchInv" prefix. This is necessary to avoid namespace conflicts with the generic invocations.

> import SEL4.API.Invocation.ARM as ArchInv
> import SEL4.API.InvocationLabels.ARM as ArchInv

\subsection{Constants}

All virtual addresses above "pptrBase" cannot be mapped by user-level tasks. With the exception of one page, at "globalsBase", they cannot be read; the globals page is mapped read-only.

> globalsBase :: VPtr
> globalsBase = VPtr 0xffffc000

The idle thread's code is at an arbitrary location in kernel memory. For convenience in the Haskell model, we place it in the globals frame, but there is no need for it to be in user-accessible memory.

> idleThreadStart :: VPtr
> idleThreadStart = globalsBase + VPtr 0x100

The idle thread executes a short loop that drains the CPU's write buffer and then waits for an interrupt. Note that the wait for interrupt instruction always completes before the interrupt is delivered, so the interrupt handler will return to the following branch instruction.

FIXME ARMHYP not checked

> idleThreadCode :: [Word]
> idleThreadCode =
>     [ 0xe3a00000 -- mov r0, \#0
>--     , 0xee070f9a -- 1: mcr p15, 0, r0, c7, c10, 4 -- drain write buffer
>--     , 0xee070f90 -- mcr p15, 0, r0, c7, c0, 4 -- wait for interrupt
>     , 0xeafffffc -- b 1b
>     ]

\subsection{Creating the vspace for the initial thread}

Function mapKernelWindow will create a virtual address space for the initial thread

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

FIXME ARMHYP this completely doesn't make any sense at the moment until we decide what to do about modeling stage 1 translations and hence the kernel map

FIXME ARMHYP as a result this entire subsection has been stripped into undefinedness to reduce clutter; it should be re-added for both ARM and ARM\_HYP once we know what to do

FIXME ARMHYP also this is BOOT CODE, adding to confusion

> mapKernelWindow :: Kernel ()
> mapKernelWindow = error "FIXME ARM_HYP BOOT unimplemented"

> mapKernelDevice :: (PAddr, PPtr Word) -> Kernel ()
> mapKernelDevice (addr, ptr) = error "FIXME ARM_HYP BOOT unimplemented"

> activateGlobalVSpace :: Kernel ()
> activateGlobalVSpace = error "FIXME ARM_HYP BOOT unimplemented"

> createITPDPTs :: Capability -> VPtr -> VPtr -> KernelInit Capability
> createITPDPTs rootCNCap vptrStart biFrameVPtr = error "FIXME ARM_HYP BOOT unimplemented"

> writeITPDPTs :: Capability -> Capability -> KernelInit ()
> writeITPDPTs rootCNCap pdCap = error "FIXME ARM_HYP BOOT unimplemented"

> createITASIDPool :: Capability -> KernelInit Capability
> createITASIDPool rootCNCap = error "FIXME ARM_HYP BOOT unimplemented"

> writeITASIDPool :: Capability -> Capability -> Kernel ()
> writeITASIDPool apCap pdCap = error "FIXME ARM_HYP BOOT unimplemented"

> mapITPTCap :: Capability -> Capability -> Kernel ()
> mapITPTCap pdCap ptCap = error "FIXME ARM_HYP BOOT unimplemented"

> mapITFrameCap :: Capability -> Capability -> Kernel ()
> mapITFrameCap pdCap frameCap = error "FIXME ARM_HYP BOOT unimplemented"

> createIPCBufferFrame :: Capability -> VPtr -> KernelInit Capability
> createIPCBufferFrame rootCNCap vptr = error "FIXME ARM_HYP BOOT unimplemented"

> createBIFrame :: Capability -> VPtr -> Word32 -> Word32 -> KernelInit Capability
> createBIFrame rootCNCap vptr nodeId numNodes = error "FIXME ARM_HYP BOOT unimplemented"

> createITFrameCap :: PPtr Word -> VPtr -> Maybe ASID -> Bool -> KernelInit Capability
> createITFrameCap pptr vptr asid large = error "FIXME ARM_HYP BOOT unimplemented"

> vptrFromPPtr :: PPtr a -> KernelInit VPtr
> vptrFromPPtr (PPtr ptr) = error "FIXME ARM_HYP BOOT unimplemented"

> createFramesOfRegion :: Capability -> Region -> Bool -> KernelInit ()
> createFramesOfRegion rootCNCap region doMap = error "FIXME ARM_HYP BOOT unimplemented"

> mapGlobalsFrame :: Kernel ()
> mapGlobalsFrame = error "FIXME ARM_HYP BOOT unimplemented"

> writeIdleCode :: Kernel ()
> writeIdleCode = error "FIXME ARM_HYP BOOT unimplemented"

> mapKernelFrame :: PAddr -> VPtr -> VMRights -> VMAttributes -> Kernel ()
> mapKernelFrame paddr vaddr vmrights attributes = error "FIXME ARM_HYP BOOT unimplemented"

> getARMGlobalPT :: Kernel (PPtr PTE)
> getARMGlobalPT = error "FIXME ARM_HYP BOOT unimplemented"

> createDeviceFrames :: Capability -> KernelInit ()
> createDeviceFrames rootCNodeCap = error "FIXME ARM_HYP BOOT unimplemented"

#else /* CONFIG_ARM_HYPERVISOR_SUPPORT */

> mapKernelWindow :: Kernel ()
> mapKernelWindow = do

An abstract version looks like:

\begin{verbatim}
  allMemory <- doMachineOp getMemoryRegions
  mapM_ mapKernelRegion allMemory
\end{verbatim}

However we assume that the result of getMemoryRegions is actually [0,1<<24] and do the following

>     let baseoffset = pptrBase `shiftR` pageBitsForSize (ARMSection)

>     let ptSize = ptBits - pteBits
>     let pdSize = pdBits - pdeBits
>     globalPD <- gets $ armKSGlobalPD . ksArchState
>     globalPTs <- gets $ armKSGlobalPTs . ksArchState
>     startentry <- return $ (PPtr (fromPPtr globalPD ))
>     deleteObjects (startentry) pdBits
>     placeNewObject (startentry) (makeObject :: PDE) pdSize
>     forM_ [baseoffset, baseoffset+16 .. (bit pdSize) - 16 - 1] $ createSectionPDE
>     forM_ [(bit pdSize) - 16, (bit pdSize) - 2] $ \offset -> do
>           let virt = offset `shiftL` pageBitsForSize (ARMSection)
>           let phys = addrFromPPtr $ PPtr $ fromVPtr virt
>           let pde = SectionPDE {
>                   pdeFrame = phys,
>                   pdeParity = True,
>                   pdeDomain = 0,
>                   pdeCacheable = True,
>                   pdeGlobal = True,
>                   pdeExecuteNever = False,
>                   pdeRights = VMKernelOnly }
>           let slot = globalPD + PPtr ((fromVPtr offset) `shiftL` pdeBits)
>           storePDE slot pde

>     let paddr = addrFromPPtr $ PPtr $ fromPPtr $ head globalPTs
>     let pde = PageTablePDE {pdeTable = paddr ,pdeParity = True, pdeDomain = 0}
>     let slot = globalPD + PPtr (((bit pdSize) - 1) `shiftL` pdeBits)
>     deleteObjects (PPtr $ fromPPtr $ head globalPTs) ptBits
>     placeNewObject (PPtr $ fromPPtr $ head globalPTs) (makeObject :: PTE) ptSize
>     storePDE slot pde

>     kernelDevices <- doMachineOp getKernelDevices
>     mapM_ mapKernelDevice kernelDevices


Helper function used above to create PDE for Section:

> createSectionPDE :: VPtr -> Kernel ()
> createSectionPDE offset = do
>     globalPD <- gets $ armKSGlobalPD . ksArchState
>     let virt = fromVPtr $ offset `shiftL` pageBitsForSize (ARMSection)
>     let phys = addrFromPPtr $ PPtr virt
>     let base = fromVPtr offset
>     let pde = SuperSectionPDE {
>             pdeFrame = phys,
>             pdeParity = True,
>             pdeCacheable = True,
>             pdeGlobal = True,
>             pdeExecuteNever = False,
>             pdeRights = VMKernelOnly }
>     let slots = map (\n -> globalPD + PPtr (n `shiftL` pdeBits))
>             [base .. base + 15]
>     (flip $ mapM_ ) slots (\slot ->  storePDE slot pde)



Any IO devices used directly by the kernel --- generally including the interrupt controller, one of the timer devices, and optionally a serial port for debugging --- must be mapped in the global address space. This implementation limits device mappings to one page; it may need to be extended to support multiple-page mappings.

> mapKernelDevice :: (PAddr, PPtr Word) -> Kernel ()
> mapKernelDevice (addr, ptr) = do
>     let vptr = VPtr $ fromPPtr ptr
>     mapKernelFrame addr vptr VMKernelOnly $ VMAttributes False False True


> activateGlobalVSpace :: Kernel ()
> activateGlobalVSpace = do
>     globalPD <- gets $ armKSGlobalPD . ksArchState
>     doMachineOp $ do
>         setCurrentPD $ addrFromPPtr globalPD
>         invalidateLocalTLB

Function pair "createITPDPTs" + "writeITPDPTs" init the memory space for the initial thread

> createITPDPTs :: Capability -> VPtr -> VPtr -> KernelInit Capability
> createITPDPTs rootCNCap vptrStart biFrameVPtr =  do
>     let pdSize = pdBits - objBits (makeObject :: PDE)
>     let ptSize = ptBits - objBits (makeObject :: PTE)
>     pdPPtr <- allocRegion pdBits
>     doKernelOp $ placeNewObject (ptrFromPAddr pdPPtr) (makeObject::PDE) pdSize -- create a pageDirectory
>     pdCap <- return $ ArchObjectCap $ PageDirectoryCap (ptrFromPAddr pdPPtr) (Just itASID)
>     slot  <- doKernelOp $ locateSlotCap rootCNCap biCapITPD
>     doKernelOp $ insertInitCap slot $ pdCap
>     slotBefore <- noInitFailure $ gets $ initSlotPosCur
>     let btmVPtr = vptrStart `shiftR` (pdSize + pageBits) `shiftL` (pdSize + pageBits)
>     let step = 1 `shiftL` (ptSize + pageBits)
>     let topVPtr = biFrameVPtr + (bit biFrameSizeBits) - 1
>     forM_ [btmVPtr,btmVPtr + step .. topVPtr] $ \vptr -> do
>         ptPPtr <- allocRegion ptBits
>         doKernelOp $ placeNewObject (ptrFromPAddr ptPPtr) (makeObject::PTE) ptSize -- create a pageTable
>         provideCap rootCNCap $ ArchObjectCap $ PageTableCap (ptrFromPAddr ptPPtr) (Just (itASID, vptr))
>     slotAfter <- noInitFailure $ gets initSlotPosCur
>     bootInfo <- noInitFailure $ gets initBootInfo
>     let bootInfo' = bootInfo {bifUIPDCaps = [slotBefore - 1 .. slotBefore - 1], bifUIPTCaps = [slotBefore .. slotAfter - 1] }
>     noInitFailure $ modify (\s -> s { initBootInfo = bootInfo' })
>     return pdCap

> writeITPDPTs :: Capability -> Capability -> KernelInit ()
> writeITPDPTs rootCNCap pdCap =
>   case pdCap of
>     ArchObjectCap cap -> do
>       doKernelOp $ copyGlobalMappings $ capPDBasePtr cap
>       ptSlots <- noInitFailure $ gets $ bifUIPTCaps . initBootInfo
>       doKernelOp $ do
>           (flip mapM) ptSlots (\pos-> do
>               slot <- locateSlotCap rootCNCap pos
>               cte <- getCTE slot
>               mapITPTCap pdCap (cteCap cte)
>            )
>       frameSlots <- noInitFailure $ gets $ bifUIFrameCaps . initBootInfo
>       doKernelOp $ do
>            (flip mapM) frameSlots (\pos -> do
>               slot <- locateSlotCap rootCNCap pos
>               cte <- getCTE slot
>               mapITFrameCap pdCap (cteCap cte))
>            slot <- locateSlotCap rootCNCap biCapITIPCBuf
>            cte <- getCTE slot
>            mapITFrameCap pdCap (cteCap cte)
>            slot <- locateSlotCap rootCNCap biCapBIFrame
>            cte <- getCTE slot
>            mapITFrameCap pdCap (cteCap cte)
>     _ -> fail $ (show pdCap) ++ " is not an ArchObjectCap."


Function pair "createITASIDPool" + "writeITASIDPool" init the asidpool cap for the initial thread

> createITASIDPool :: Capability -> KernelInit Capability
> createITASIDPool rootCNCap = do
>     apPPtr <- allocRegion $ objBits (undefined :: ASIDPool)
>     doKernelOp $ placeNewObject (ptrFromPAddr apPPtr) (makeObject::ASIDPool) 0
>     slot <- doKernelOp $ locateSlotCap rootCNCap biCapITASIDPool
>     asidPoolCap <- return $ ArchObjectCap $ ASIDPoolCap (ptrFromPAddr apPPtr) 0
>     doKernelOp $ insertInitCap slot asidPoolCap
>     slot <- doKernelOp $ locateSlotCap rootCNCap biCapASIDControl
>     asidControlCap <- return $ ArchObjectCap $ ASIDControlCap
>     doKernelOp $ insertInitCap slot asidControlCap
>     return asidPoolCap

> writeITASIDPool :: Capability -> Capability -> Kernel ()
> writeITASIDPool apCap pdCap = do
>     apPtr <- case apCap of
>                    ArchObjectCap (ASIDPoolCap ptr _) -> return ptr
>                    _ -> fail "WrieITASIDPool:should never happen"
>     pdPtr <- case pdCap of
>                    ArchObjectCap (PageDirectoryCap ptr _) -> return ptr
>                    _ -> fail "WriteITASIDPool:should never happen"
>     ASIDPool ap <- getObject apPtr
>     let ap' = ap//[(itASID, Just pdPtr)]
>     setObject apPtr (ASIDPool ap')
>     asidTable <- gets (armKSASIDTable . ksArchState)
>     let asidTable' = asidTable//[(asidHighBitsOf itASID, Just apPtr)]
>     modify (\s -> s {
>          ksArchState = (ksArchState s) { armKSASIDTable = asidTable' }})
>

Function "mapITPTCap" is used to store a pde into the pd of the initial thread

> mapITPTCap :: Capability -> Capability -> Kernel ()
> mapITPTCap pdCap ptCap = do
>     pd <- case pdCap of
>               ArchObjectCap (PageDirectoryCap ptr _) -> return ptr
>               _ -> fail "mapITPTCap:should never happen"
>     ptCap' <- case ptCap of
>                   ArchObjectCap c -> return c
>                   _ -> fail "mapITPTCap:should never happen"
>     (pt,vptr) <- case ptCap' of
>                             PageTableCap { capPTBasePtr = pt',
>                                            capPTMappedAddress = Just (_, vptr') }
>                               -> return (pt', vptr')
>                             _ -> fail $ "mapITPTCap:This shouldn't happen. PageTableCap expected instead of" ++ (show ptCap)
>     let offset = fromVPtr $ vptr `shiftR` pageBitsForSize ARMSection
>     let targetSlot = pd + (PPtr $ offset `shiftL` 2) -- array entry size
>     let pde = PageTablePDE {
>             pdeTable = addrFromPPtr pt,
>             pdeParity = True,
>             pdeDomain = 0 }
>     storePDE targetSlot pde

Function "mapITFrameCap" maps pte into pt of the initial thread.

> mapITFrameCap :: Capability -> Capability -> Kernel ()
> mapITFrameCap pdCap frameCap = do
>     pd' <- case pdCap of
>                ArchObjectCap (PageDirectoryCap ptr _) -> return ptr
>                _ -> fail $ "mapITFrameCap: expect PDCap , get:" ++ (show pdCap)
>     frameCap' <- case frameCap of
>                      ArchObjectCap c -> return c
>                      _ -> fail $ "mapITFrameCap: expect FrameCap, get:" ++ (show frameCap)
>     (frame,vptr) <- case frameCap' of
>                               PageCap { capVPBasePtr = frame',
>                                         capVPMappedAddress = Just (_, vptr') }
>                                   -> return (frame', vptr')
>                               _ -> fail $ "This shouldn't happen, PageCap expected instead of " ++ (show frameCap)
>     let offset = fromVPtr $ vptr `shiftR` pageBitsForSize ARMSection
>     let pd = pd' + (PPtr $ offset `shiftL` 2)
>     pde <- getObject pd
>     pt <- case pde of
>                      PageTablePDE { pdeTable = ref } -> return $ ptrFromPAddr ref
>                      _ -> fail $ "This shouldn't happen,expect PageTablePDE at " ++ (show pd) ++ "instead of " ++ (show pde)
>     let offset = fromVPtr $ ((vptr .&.(mask $ pageBitsForSize ARMSection))
>                                `shiftR` pageBitsForSize ARMSmallPage)
>     let targetSlot = pt + (PPtr $ offset `shiftL` 2) -- slot size
>     let pte = SmallPagePTE {
>             pteFrame = addrFromPPtr frame,
>             pteCacheable = True,
>             pteGlobal = False,
>             pteExecuteNever = False,
>             pteRights = VMReadWrite }
>     storePTE targetSlot pte

Function "createIPCBufferFrame" will create IpcBuffer frame of the initial thread.
The address of this ipcbuffer  starts from the end of uiRegion

> createIPCBufferFrame :: Capability -> VPtr -> KernelInit Capability
> createIPCBufferFrame rootCNCap vptr = do
>       pptr <- allocFrame
>       doKernelOp $ doMachineOp $ clearMemory (ptrFromPAddr pptr) (1 `shiftL` pageBits)
>       cap <- createITFrameCap (ptrFromPAddr pptr) vptr (Just itASID) False
>       slot <- doKernelOp $ locateSlotCap rootCNCap biCapITIPCBuf
>       doKernelOp $ insertInitCap slot cap
>       bootInfo <- noInitFailure $ gets (initBootInfo)
>       let bootInfo' = bootInfo { bifIPCBufVPtr = vptr}
>       noInitFailure $ modify (\s -> s {initBootInfo = bootInfo' })
>       return cap

Function "createBIFrame" will create the biframe cap for the initial thread

> createBIFrame :: Capability -> VPtr -> Word32 -> Word32 -> KernelInit Capability
> createBIFrame rootCNCap vptr nodeId numNodes = do
>       pptr <- allocFrame
>       bootInfo <- noInitFailure $ gets initBootInfo
>       let bootInfo' = bootInfo { bifNodeID = nodeId,
>                                  bifNumNodes = numNodes }
>       noInitFailure $ modify (\s -> s {
>           initBootInfo = bootInfo',
>           initBootInfoFrame = pptr,
>           initSlotPosCur = biCapDynStart
>           })
>       doKernelOp $ doMachineOp $ clearMemory (ptrFromPAddr pptr) (1 `shiftL` pageBits)
>       cap <- createITFrameCap (ptrFromPAddr pptr) vptr (Just itASID) False
>       slot <- doKernelOp $ locateSlotCap rootCNCap biCapBIFrame
>       doKernelOp $ insertInitCap slot cap
>       return cap

> createITFrameCap :: PPtr Word -> VPtr -> Maybe ASID -> Bool -> KernelInit Capability
> createITFrameCap pptr vptr asid large = do
>     let sz = if large then ARMLargePage else ARMSmallPage
>     let addr = case asid of
>                     Just asid' -> Just (asid', vptr)
>                     Nothing -> Nothing
>     let frame = PageCap {
>              capVPIsDevice = False,
>              capVPBasePtr = pptr,
>              capVPRights = VMReadWrite,
>              capVPSize = sz,
>              capVPMappedAddress = addr }
>     return $ ArchObjectCap $ frame

> vptrFromPPtr :: PPtr a -> KernelInit VPtr
> vptrFromPPtr (PPtr ptr) = do
>     offset <- gets initVPtrOffset
>     return $ (VPtr ptr) + offset

> createFramesOfRegion :: Capability -> Region -> Bool -> KernelInit ()
> createFramesOfRegion rootCNCap region doMap = do
>     curSlotPos <- noInitFailure $ gets initSlotPosCur
>     (startPPtr, endPPtr) <- return $ fromRegion region
>     forM_ [startPPtr,startPPtr + (bit pageBits) .. endPPtr] $ \ptr -> do
>         vptr <- vptrFromPPtr $ ptr
>         frameCap <- if doMap then
>                     createITFrameCap ptr vptr (Just itASID) False
>                     else createITFrameCap ptr 0 Nothing False
>         provideCap rootCNCap frameCap
>     slotPosAfter <- noInitFailure $ gets initSlotPosCur
>     bootInfo <- noInitFailure $ gets initBootInfo
>     let bootInfo' = bootInfo { bifUIFrameCaps = [curSlotPos .. slotPosAfter - 1] }
>     noInitFailure $ modify (\s -> s { initBootInfo = bootInfo' })


The "mapKernelFrame" helper function is used when mapping the globals frame, kernel IO devices, and the trap frame. We simply store pte into our globalPT

> mapKernelFrame :: PAddr -> VPtr -> VMRights -> VMAttributes -> Kernel ()
> mapKernelFrame paddr vaddr vmrights attributes = do
>     let idx = fromVPtr $ ( (vaddr .&. (mask $ pageBitsForSize ARMSection))
>                           `shiftR` pageBitsForSize ARMSmallPage)
>     globalPT <- getARMGlobalPT
>     let pte = SmallPagePTE {
>                  pteFrame = paddr,
>                  pteCacheable = armPageCacheable attributes,
>                  pteGlobal = True,
>                  pteExecuteNever = False,
>                  pteRights = vmrights }
>     storePTE (PPtr ((fromPPtr globalPT) + (idx `shiftL` 2))) pte

> getARMGlobalPT :: Kernel (PPtr PTE)
> getARMGlobalPT = do
>     pt <- gets (head . armKSGlobalPTs . ksArchState)
>     return pt

> createDeviceFrames :: Capability -> KernelInit ()
> createDeviceFrames rootCNodeCap = do
>     deviceRegions <- doKernelOp $ doMachineOp getDeviceRegions
>     (flip mapM_) deviceRegions (\(start,end) -> do
>         frameSize <- return $ if (isAligned start (pageBitsForSize ARMSection))
>                          && isAligned end (pageBitsForSize ARMSection)
>             then ARMSection else ARMSmallPage
>         slotBefore <- noInitFailure $ gets initSlotPosCur
>         (flip mapM_) [start, (start + (bit (pageBitsForSize frameSize))) .. (end - 1)]
>               (\f -> do
>                   frameCap <- createITFrameCap (ptrFromPAddr f) 0 Nothing (frameSize == ARMSection)
>                   provideCap rootCNodeCap frameCap)
>         slotAfter <- noInitFailure $ gets initSlotPosCur
>         let biDeviceRegion = BIDeviceRegion {
>                                   bidrBasePAddr = start,
>                                   bidrFrameSizeBits = fromIntegral $ pageBitsForSize frameSize,
>                                   bidrFrameCaps = SlotRegion (slotBefore, slotAfter) }
>         devRegions <- noInitFailure $ gets (bifDeviceRegions . initBootInfo)
>         let devRegions' = devRegions ++ [biDeviceRegion]
>         bootInfo <- noInitFailure $ gets (initBootInfo)
>         let bootInfo' = bootInfo { bifDeviceRegions = devRegions' }
>         noInitFailure $ modify (\st -> st { initBootInfo = bootInfo' })
>         )
>     bInfo <- noInitFailure $ gets (initBootInfo)
>     let bInfo' = bInfo { bifNumDeviceRegions = (fromIntegral . length . bifDeviceRegions) bInfo }
>     noInitFailure $ modify (\st -> st { initBootInfo = bInfo' })

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

\subsubsection{Creating a New Address Space}

With hypervisor extensions, kernel and user MMUs are completely independent. However, we still need to share the globals page.

> copyGlobalMappings :: PPtr PDE -> Kernel ()
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> copyGlobalMappings newPD = return ()
#else
> copyGlobalMappings newPD = do
>     globalPD <- gets (armKSGlobalPD . ksArchState)
>     let pdSize = 1 `shiftL` (pdBits - pdeBits)
>     forM_ [fromVPtr pptrBase `shiftR` 20 .. pdSize - 1] $ \index -> do
>         let offset = PPtr index `shiftL` pdeBits
>         pde <- getObject (globalPD + offset)
>         storePDE (newPD + offset) pde
#endif

\subsection{Creating and Updating Mappings}

When a frame is being mapped, or an existing mapping updated, the following function is used to locate the page table or page directory slots that will be updated and to construct the entry that will be written into them.

> largePagePTEOffsets :: [PPtr PTE]
> largePagePTEOffsets = [0, PPtr pts .. PPtr (15 `shiftL` pteBits)]
>     where pts = bit pteBits
> superSectionPDEOffsets :: [PPtr PDE]
> superSectionPDEOffsets = [0, PPtr pds .. PPtr (15 `shiftL` pdeBits)]
>     where pds = bit pdeBits

> createMappingEntries :: PAddr -> VPtr ->
>     VMPageSize -> VMRights -> VMAttributes -> PPtr PDE ->
>     KernelF SyscallError (Either (PTE, [PPtr PTE]) (PDE, [PPtr PDE]))
> createMappingEntries base vptr ARMSmallPage vmRights attrib pd = do
>     p <- lookupErrorOnFailure False $ lookupPTSlot pd vptr
>     return $ Left (SmallPagePTE {
>         pteFrame = base,
>         pteCacheable = armPageCacheable attrib,
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>         pteGlobal = False,
#endif
>         pteExecuteNever = armExecuteNever attrib,
>         pteRights = vmRights }, [p])
>
> createMappingEntries base vptr ARMLargePage vmRights attrib pd = do
>     p <- lookupErrorOnFailure False $ lookupPTSlot pd vptr
>     return $ Left (LargePagePTE {
>         pteFrame = base,
>         pteCacheable = armPageCacheable attrib,
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>         pteGlobal = False,
#endif
>         pteExecuteNever = armExecuteNever attrib,
>         pteRights = vmRights }, map (+p) largePagePTEOffsets)
>
> createMappingEntries base vptr ARMSection vmRights attrib pd = do
>     let p = lookupPDSlot pd vptr
>     return $ Right (SectionPDE {
>         pdeFrame = base,
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>         pdeParity = armParityEnabled attrib,
>         pdeDomain = 0,
#endif
>         pdeCacheable = armPageCacheable attrib,
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>         pdeGlobal = False,
#endif
>         pdeExecuteNever = armExecuteNever attrib,
>         pdeRights = vmRights }, [p])
>
> createMappingEntries base vptr ARMSuperSection vmRights attrib pd = do
>     let p = lookupPDSlot pd vptr
>     return $ Right (SuperSectionPDE {
>         pdeFrame = base,
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>         pdeParity = armParityEnabled attrib,
#endif
>         pdeCacheable = armPageCacheable attrib,
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>         pdeGlobal = False,
#endif
>         pdeExecuteNever = armExecuteNever attrib,
>         pdeRights = vmRights }, map (+p) superSectionPDEOffsets)

The following function is called before creating or modifying mappings in a page table or page directory, and is responsible for ensuring that the mapping is safe --- that is, that inserting it will behave predictably and will not damage the hardware. The ARMv6 specifications require that there are never two mappings of different sizes at any virtual address in the active address space, so this function will throw a fault if the requested operation would change the size of the mapping of any existing valid entry.

> ensureSafeMapping :: Either (PTE, [PPtr PTE]) (PDE, [PPtr PDE]) ->
>     KernelF SyscallError ()

> ensureSafeMapping (Left (InvalidPTE, _)) = return ()
>
> ensureSafeMapping (Left (SmallPagePTE {}, ptSlots)) =
>     forM_ ptSlots $ \slot -> do
>         pte <- withoutFailure $ getObject slot
>         case pte of
>             InvalidPTE -> return ()
>             SmallPagePTE {} -> return ()
>             _ -> throw DeleteFirst
>
> ensureSafeMapping (Left (LargePagePTE {}, ptSlots)) =
>     forM_ ptSlots $ \slot -> do
>         pte <- withoutFailure $ getObject slot
>         case pte of
>             InvalidPTE -> return ()
>             LargePagePTE {} -> return ()
>             _ -> throw DeleteFirst

> ensureSafeMapping (Right (InvalidPDE, _)) = return ()
>
> ensureSafeMapping (Right (PageTablePDE {}, _)) =
>     fail "This function is not called when mapping page tables"
>
> ensureSafeMapping (Right (SectionPDE {}, pdSlots)) =
>     forM_ pdSlots $ \slot -> do
>         pde <- withoutFailure $ getObject slot
>         case pde of
>             InvalidPDE -> return ()
>             SectionPDE {} -> return ()
>             _ -> throw DeleteFirst
>
> ensureSafeMapping (Right (SuperSectionPDE {}, pdSlots)) =
>     forM_ pdSlots $ \slot -> do
>         pde <- withoutFailure $ getObject slot
>         case pde of
>             InvalidPDE -> return ()
>             SuperSectionPDE {} -> return ()
>             _ -> throw DeleteFirst

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

> findPDForASID :: ASID -> KernelF LookupFailure (PPtr PDE)
> findPDForASID asid = do
>     assert (asid > 0) "ASID 0 is used for objects that are not mapped"
>     assert (asid <= snd asidRange) "ASID out of range"
>     asidTable <- withoutFailure $ gets (armKSASIDTable . ksArchState)
>     let poolPtr = asidTable!(asidHighBitsOf asid)
>     ASIDPool pool <- case poolPtr of
>         Just ptr -> withoutFailure $ getObject ptr
>         Nothing -> throw InvalidRoot
>     let pd = pool!(asid .&. mask asidLowBits)
>     case pd of
>         Just ptr -> do
>             assert (ptr /= 0) "findPDForASID: found null PD"
>             withoutFailure $ checkPDAt ptr
>             return ptr
>         Nothing -> throw InvalidRoot

This version of findPDForASID will fail rather than raise an exception if the ASID does not look up a page directory.

> findPDForASIDAssert :: ASID -> Kernel (PPtr PDE)
> findPDForASIDAssert asid = do
>     pd <- findPDForASID asid `catchFailure`
>         const (fail "findPDForASIDAssert: pd not found")
>     assert (pd .&. mask pdBits == 0)
>         "findPDForASIDAssert: page directory pointer alignment check"
>     checkPDAt pd
>     checkPDUniqueToASID pd asid
>     asidMap <- gets (armKSASIDMap . ksArchState)
>     flip assert "findPDForASIDAssert: page directory map mismatch"
>         $ case asidMap ! asid of
>             Nothing -> True
>             Just (_, pd') -> pd == pd'
>     return pd

These checks are too expensive to run in haskell. The first function checks that the pointer is to a page directory, which would require testing that each entry of the table is present. The second checks that the page directory appears in armKSASIDMap only on the ASIDs specified, which would require walking all possible ASIDs to test. In the formalisation of this specification, these functions are given alternative definitions that make the appropriate checks.

> checkPDAt :: PPtr PDE -> Kernel ()
> checkPDAt _ = return ()

> checkPTAt :: PPtr PTE -> Kernel ()
> checkPTAt _ = return ()

> checkPDASIDMapMembership :: PPtr PDE -> [ASID] -> Kernel ()
> checkPDASIDMapMembership _ _ = return ()

> checkPDUniqueToASID :: PPtr PDE -> ASID -> Kernel ()
> checkPDUniqueToASID pd asid = checkPDASIDMapMembership pd [asid]

> checkPDNotInASIDMap :: PPtr PDE -> Kernel ()
> checkPDNotInASIDMap pd = checkPDASIDMapMembership pd []

\subsubsection{Locating Page Table and Page Directory Slots}

The "lookupPTSlot" function locates the page table slot that maps a given virtual address, and returns a pointer to the slot. It will throw a lookup failure if the required page directory slot does not point to a page table.

FIXME ARMHYP the normal ARM has magic numbers everywhere here! can't be certain these are all right now

> lookupPTSlot :: PPtr PDE -> VPtr -> KernelF LookupFailure (PPtr PTE)
> lookupPTSlot pd vptr = do
>     let pdSlot = lookupPDSlot pd vptr
>     pde <- withoutFailure $ getObject pdSlot
>     case pde of
>         PageTablePDE {} -> do
>             let pt = ptrFromPAddr $ pdeTable pde
>             withoutFailure $ lookupPTSlotFromPT pt vptr
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>         _ -> throw $ MissingCapability 21
#else
>         _ -> throw $ MissingCapability 20
#endif

> lookupPTSlotFromPT :: PPtr PTE -> VPtr -> Kernel (PPtr PTE)
> lookupPTSlotFromPT pt vptr = do
>     let ptIndex = fromVPtr $ vptr `shiftR` pageBits .&. mask (ptBits - pteBits)
>     let ptSlot = pt + (PPtr $ ptIndex `shiftL` pteBits)
>     checkPTAt pt
>     return ptSlot

Similarly, "lookupPDSlot" locates a slot in the top-level page directory. However, it does not access the kernel state and never throws a fault, so it is not in the kernel monad.

> lookupPDSlot :: PPtr PDE -> VPtr -> PPtr PDE
> lookupPDSlot pd vptr =
>     let pdIndex = fromVPtr $ vptr `shiftR` (pageBits + ptBits - pteBits)
>     in pd + (PPtr $ pdIndex `shiftL` pdeBits)

\subsubsection{Handling Faults}

If the kernel receives a VM fault from the CPU, it must determine the address and cause of the fault and then throw it to the user-level fault handler. The C datastructure to store the cause of the fault has only 12 bits space, hence the mask. Only the lower bits are significant anyway.

Hypervisor mode requires extra translation here.

> handleVMFault :: PPtr TCB -> VMFaultType -> KernelF Fault ()
> handleVMFault _ ARMDataAbort = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     addr <- withoutFailure $ doMachineOp getHDFAR
>     uaddr <- withoutFailure $ doMachineOp (addressTranslateS1 addr)
>     let faddr = (uaddr .&. complement (mask pageBits)) .|.
>                 (addr .&. mask pageBits)
>     fault <- withoutFailure $ doMachineOp getHSR
>     throw $ ArchFault $ VMFault faddr [0, fault .&. 0x3ffffff]
#else
>     addr <- withoutFailure $ doMachineOp getFAR
>     fault <- withoutFailure $ doMachineOp getDFSR
>     throw $ ArchFault $ VMFault addr [0, fault .&. mask 14]
#endif
>
> handleVMFault thread ARMPrefetchAbort = do
>     pc <- withoutFailure $ asUser thread $ getRestartPC
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     upc <- withoutFailure $ doMachineOp (addressTranslateS1 $ VPtr pc)
>     let faddr = (upc .&. complement (mask pageBits)) .|.
>                 (VPtr pc .&. mask pageBits)
>     fault <- withoutFailure $ doMachineOp getHSR
>     throw $ ArchFault $ VMFault faddr [1, fault .&. 0x3ffffff]
#else
>     fault <- withoutFailure $ doMachineOp getIFSR
>     throw $ ArchFault $ VMFault (VPtr pc) [1, fault .&. mask 14]
#endif

\subsection{Unmapping and Deletion}

When a capability backing a virtual memory mapping is deleted, or when an explicit request is made to remove a mapping, the kernel must locate the corresponding entries in the page table or ASID table and remove them. It is also necessary to flush the removed mappings from the hardware caches.

\subsubsection{Deleting an ASID Pool}

> deleteASIDPool :: ASID -> PPtr ASIDPool -> Kernel ()
> deleteASIDPool base ptr = do
>     assert (base .&. mask asidLowBits == 0)
>         "ASID pool's base must be aligned"
>     asidTable <- gets (armKSASIDTable . ksArchState)
>     when (asidTable!(asidHighBitsOf base) == Just ptr) $ do
>         ASIDPool pool <- getObject ptr
>         forM [0 .. (bit asidLowBits) - 1] $ \offset -> do
>             when (isJust $ pool ! offset) $ do
>                 flushSpace $ base + offset
>                 invalidateASIDEntry $ base + offset
>         let asidTable' = asidTable//[(asidHighBitsOf base, Nothing)]
>         modify (\s -> s {
>             ksArchState = (ksArchState s) { armKSASIDTable = asidTable' }})
>         tcb <- getCurThread
>         setVMRoot tcb

\subsubsection{Deleting an Address Space}

> deleteASID :: ASID -> PPtr PDE -> Kernel ()
> deleteASID asid pd = do
>     asidTable <- gets (armKSASIDTable . ksArchState)
>     case asidTable!(asidHighBitsOf asid) of
>         Nothing -> return ()
>         Just poolPtr -> do
>             ASIDPool pool <- getObject poolPtr
>             when (pool!(asid .&. mask asidLowBits) == Just pd) $ do
>                 flushSpace asid
>                 invalidateASIDEntry asid
>                 let pool' = pool//[(asid .&. mask asidLowBits, Nothing)]
>                 setObject poolPtr $ ASIDPool pool'
>                 tcb <- getCurThread
>                 setVMRoot tcb

\subsubsection{Deleting a Page Table}

> pageTableMapped :: ASID -> VPtr -> PPtr PTE -> Kernel (Maybe (PPtr PDE))
> pageTableMapped asid vaddr pt = catchFailure
>     (do
>         pd <- findPDForASID asid
>         let pdSlot = lookupPDSlot pd vaddr
>         pde <- withoutFailure $ getObject pdSlot
>         case pde of
>             PageTablePDE { pdeTable = pt' } -> return $
>                 if pt' == addrFromPPtr pt then Just pd else Nothing
>             _ -> return Nothing)
>     (\_ -> return Nothing)

> unmapPageTable :: ASID -> VPtr -> PPtr PTE -> Kernel ()
> unmapPageTable asid vaddr pt = do
>     maybePD <- pageTableMapped asid vaddr pt
>     case maybePD of
>         Just pd -> do
>             let pdSlot = lookupPDSlot pd vaddr
>             storePDE pdSlot InvalidPDE
>             doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr pdSlot) (addrFromPPtr pdSlot)
>             flushTable pd asid vaddr
>         Nothing -> return ()

\subsubsection{Unmapping a Frame}

FIXME ARMHYP checks contiguous hint here, but that should be built into the getObject inside checkMappingPPtr

> unmapPage :: VMPageSize -> ASID -> VPtr -> PPtr Word -> Kernel ()
> unmapPage size asid vptr ptr = ignoreFailure $ do
>     pd <- findPDForASID asid
>     case size of
>         ARMSmallPage -> do
>             p <- lookupPTSlot pd vptr
>             checkMappingPPtr ptr size (Left p)
>             withoutFailure $ do
>                 storePTE p InvalidPTE
>                 doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr p) (addrFromPPtr p)
>         ARMLargePage -> do
>             p <- lookupPTSlot pd vptr
>             checkMappingPPtr ptr size (Left p)
>             withoutFailure $ do
>                 let slots = map (+p) largePagePTEOffsets
>                 mapM (flip storePTE InvalidPTE) slots
>                 doMachineOp $
>                     cleanCacheRange_PoU (VPtr $ fromPPtr $ (head slots))
>                                         (VPtr $ (fromPPtr (last slots)) + (bit pteBits - 1))
>                                         (addrFromPPtr (head slots))
>         ARMSection -> do
>             let p = lookupPDSlot pd vptr
>             checkMappingPPtr ptr size (Right p)
>             withoutFailure $ do
>                 storePDE p InvalidPDE
>                 doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr p) (addrFromPPtr p)
>         ARMSuperSection -> do
>             let p = lookupPDSlot pd vptr
>             checkMappingPPtr ptr size (Right p)
>             withoutFailure $ do
>                 let slots = map (+p) superSectionPDEOffsets
>                 mapM (flip storePDE InvalidPDE) slots
>                 doMachineOp $
>                     cleanCacheRange_PoU (VPtr $ fromPPtr $ (head slots))
>                                         (VPtr $ (fromPPtr (last slots)) + (bit pdeBits - 1))
>                                         (addrFromPPtr (head slots))
>     withoutFailure $ flushPage size pd asid vptr

This helper function checks that the mapping installed at a given PT or PD slot points at the given physical address. If that is not the case, the mapping being unmapped has already been displaced, and the unmap need not be performed.

> checkMappingPPtr :: PPtr Word -> VMPageSize ->
>                 Either (PPtr PTE) (PPtr PDE) -> KernelF LookupFailure ()
> checkMappingPPtr pptr size (Left pt) = do
>     pte <- withoutFailure $ getObject pt
>     case (pte, size) of
>         (SmallPagePTE { pteFrame = base }, ARMSmallPage) ->
>             unless (base == addrFromPPtr pptr) $ throw InvalidRoot
>         (LargePagePTE { pteFrame = base }, ARMLargePage) ->
>             unless (base == addrFromPPtr pptr) $ throw InvalidRoot
>         _ -> throw InvalidRoot
> checkMappingPPtr pptr size (Right pd) = do
>     pde <- withoutFailure $ getObject pd
>     case (pde, size) of
>         (SectionPDE { pdeFrame = base }, ARMSection) ->
>             unless (base == addrFromPPtr pptr) $ throw InvalidRoot
>         (SuperSectionPDE { pdeFrame = base }, ARMSuperSection) ->
>             unless (base == addrFromPPtr pptr) $ throw InvalidRoot
>         _ -> throw InvalidRoot


> armv_contextSwitch_HWASID :: PPtr PDE -> HardwareASID -> MachineMonad ()
> armv_contextSwitch_HWASID pd hwasid = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>    writeContextIDAndPD hwasid (addrFromPPtr pd)
#else
>    setCurrentPD $ addrFromPPtr pd
>    setHardwareASID hwasid
#endif

> armv_contextSwitch :: PPtr PDE -> ASID -> Kernel ()
> armv_contextSwitch pd asid = do
>    hwasid <- getHWASID asid
>    doMachineOp $ armv_contextSwitch_HWASID pd hwasid

\subsection{Address Space Switching}

When switching threads, or after deleting an ASID or page directory, the kernel must locate the current thread's page directory, check the validity of the thread's ASID, and set the hardware's ASID and page directory registers.

If the current thread has no page directory, or if it has an invalid ASID, the hardware page directory register is set to the global page directory, which contains only kernel mappings. In this case it is not necessary to set the current ASID, since the valid mappings are all global.

> setVMRoot :: PPtr TCB -> Kernel ()
> setVMRoot tcb = do
>     threadRootSlot <- getThreadVSpaceRoot tcb
>     threadRoot <- getSlotCap threadRootSlot
>     catchFailure
>         (case threadRoot of
>             ArchObjectCap (PageDirectoryCap {
>                     capPDMappedASID = Just asid,
>                     capPDBasePtr = pd }) -> do
>                 pd' <- findPDForASID asid
>                 when (pd /= pd') $ do
>                     throw InvalidRoot
>                 withoutFailure $ do
>                     armv_contextSwitch pd asid
>             _ -> throw InvalidRoot)
>         (\_ -> do
>             case threadRoot of
>                 ArchObjectCap (PageDirectoryCap {
>                     capPDMappedASID = Just _,
>                     capPDBasePtr = pd }) -> checkPDNotInASIDMap pd
>                 _ -> return ()
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>             globalPD <- gets (armUSGlobalPD . ksArchState)
#else
>             globalPD <- gets (armKSGlobalPD . ksArchState)
#endif
>             doMachineOp $ setCurrentPD $ addrFromKPPtr globalPD)

When cleaning the cache by user virtual address on ARM11, the active address space must be the one that contains the mappings being cleaned. The following function is used to temporarily switch to a given page directory and ASID, in order to clean the cache. It returns "True" if the address space was not the same as the current one, in which case the caller must switch back to the current address space once the cache is clean.

> setVMRootForFlush :: PPtr PDE -> ASID -> Kernel Bool
> setVMRootForFlush pd asid = do
>     tcb <- getCurThread
>     threadRootSlot <- getThreadVSpaceRoot tcb
>     threadRoot <- getSlotCap threadRootSlot
>     case threadRoot of
>         ArchObjectCap (PageDirectoryCap {
>                 capPDMappedASID = Just _,
>                 capPDBasePtr = cur_pd }) | cur_pd == pd -> return False
>         _ -> do
>             armv_contextSwitch pd asid
>             return True

\subsection{Helper Functions}

The VSpace root must be an ARM page directory with an ASID allocated.

Note that this does not check that the ASID is valid, so invalid-root faults are still possible after setting this capability as the root. This is because the ASID may become invalid at any time. % XXX fix this

> isValidVTableRoot :: Capability -> Bool
> isValidVTableRoot
>     (ArchObjectCap (PageDirectoryCap { capPDMappedASID = Just _ })) = True
> isValidVTableRoot _ = False

The location of an IPC buffer is computed using the relevant bits of a VPtr as an offset within a frame.
The IPC buffer frame must be an ARM frame capability, and the buffer must be aligned.

Note that implementations with separate high and low memory regions may also wish to limit valid IPC buffer frames to low memory, so the kernel can access them without extra mappings. This function may also be used to enforce cache colouring restrictions.

> checkValidIPCBuffer :: VPtr -> Capability -> KernelF SyscallError ()
> checkValidIPCBuffer vptr (ArchObjectCap (PageCap {capVPIsDevice = False})) = do
>     when (vptr .&. mask msgAlignBits /= 0) $ throw AlignmentError
>     return ()
> checkValidIPCBuffer _ _ = throw IllegalOperation

ARM memory mappings may be read-only or read-write; on newer revisions of the ARM they may also be marked non-executable. Write-only mappings are not possible.

> maskVMRights :: VMRights -> CapRights -> VMRights
> maskVMRights r m = case (r, capAllowRead m, capAllowWrite m) of
>     (VMNoAccess, _, _) -> VMNoAccess
>     (VMReadOnly, True, _) -> VMReadOnly
>     (VMReadWrite, True, False) -> VMReadOnly
>     (VMReadWrite, True, True) -> VMReadWrite
>     _ -> VMKernelOnly

ARM memory mappings may be marked cacheable or non-cacheable. Also, parity checking can be enabled or disabled at a page table level.

> attribsFromWord :: Word -> VMAttributes
> attribsFromWord w = VMAttributes {
>     armPageCacheable = w `testBit` 0,
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     armParityEnabled = False,
#else
>     armParityEnabled = w `testBit` 1,
#endif
>     armExecuteNever = w `testBit` 2 }

\subsection{ARM Hardware ASID allocation}

Manage the stored HW ASID.

XXX ARMHYP no changes in this subsection

> storeHWASID :: ASID -> HardwareASID -> Kernel ()
> storeHWASID asid hw_asid = do
>     pd <- findPDForASIDAssert asid
>     asidMap <- gets (armKSASIDMap . ksArchState)
>     let asidMap' = asidMap//[(asid, Just (hw_asid, pd))]
>     modify (\s -> s {
>         ksArchState = (ksArchState s)
>         { armKSASIDMap = asidMap' }})
>     hwASIDMap <- gets (armKSHWASIDTable . ksArchState)
>     let hwASIDMap' = hwASIDMap//[(hw_asid, Just asid)]
>     modify (\s -> s {
>         ksArchState = (ksArchState s)
>         { armKSHWASIDTable = hwASIDMap' }})

> loadHWASID :: ASID -> Kernel (Maybe HardwareASID)
> loadHWASID asid = do
>     asidMap <- gets (armKSASIDMap . ksArchState)
>     findPDForASIDAssert asid
>     return $ case asidMap ! asid of
>         Nothing -> Nothing
>         Just (hw_asid, _) -> Just hw_asid

> invalidateASID :: ASID -> Kernel ()
> invalidateASID asid = do
>     findPDForASIDAssert asid
>     asidMap <- gets (armKSASIDMap . ksArchState)
>     let asidMap' = asidMap//[(asid, Nothing)]
>     modify (\s -> s {
>         ksArchState = (ksArchState s)
>         { armKSASIDMap = asidMap' }})

> invalidateHWASIDEntry :: HardwareASID -> Kernel ()
> invalidateHWASIDEntry hwASID = do
>     asidMap <- gets (armKSHWASIDTable . ksArchState)
>     let asidMap' = asidMap//[(hwASID, Nothing)]
>     modify (\s -> s {
>         ksArchState = (ksArchState s)
>         { armKSHWASIDTable = asidMap' }})

> invalidateASIDEntry :: ASID -> Kernel ()
> invalidateASIDEntry asid = do
>     maybeHWASID <- loadHWASID asid
>     when (isJust maybeHWASID) $ invalidateHWASIDEntry (fromJust maybeHWASID)
>     invalidateASID asid


> findFreeHWASID :: Kernel HardwareASID
> findFreeHWASID = do

Look for a free Hardware ASID.

>     hwASIDTable <- gets (armKSHWASIDTable . ksArchState)
>     nextASID <- gets (armKSNextASID . ksArchState)
>     let maybe_asid = find (\a -> isNothing (hwASIDTable ! a))
>                       ([nextASID .. maxBound] ++ init [minBound .. nextASID])

If there is one, return it, otherwise revoke the next one in a strict
round-robin.

>     case maybe_asid of
>         Just hw_asid -> return hw_asid
>         Nothing -> do
>             invalidateASID $ fromJust $ hwASIDTable ! nextASID
>             doMachineOp $ invalidateLocalTLB_ASID nextASID
>             invalidateHWASIDEntry nextASID
>             let new_nextASID =
>                     if nextASID == maxBound
>                     then minBound
>                     else nextASID + 1
>             modify (\s -> s {
>                 ksArchState = (ksArchState s)
>                 { armKSNextASID = new_nextASID }})
>             return nextASID

> getHWASID :: ASID -> Kernel HardwareASID
> getHWASID asid = do
>     maybe_hw_asid <- loadHWASID asid
>     case maybe_hw_asid of
>         Just hw_asid ->
>             return hw_asid
>         Nothing -> do
>             new_hw_asid <- findFreeHWASID
>             storeHWASID asid new_hw_asid
>             return new_hw_asid

\subsection {ARM Cache and TLB consistency}

FIXME ARMHYP TODO unify hyp/non-hyp to share more code

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> doFlush :: FlushType -> VPtr -> VPtr -> PAddr -> MachineMonad ()
> doFlush flushType vstart vend pstart =
>     case flushType of
>         Clean           -> cleanCacheRange_RAM vstart' vend' pstart
>         Invalidate      -> invalidateCacheRange_RAM vstart' vend' pstart
>         CleanInvalidate -> cleanInvalidateCacheRange_RAM vstart' vend' pstart
>         Unify           -> do
>                      cleanCacheRange_PoU vstart' vend' pstart
>                      dsb
>                      invalidateCacheRange_I vstart' vend' pstart
>                      branchFlushRange vstart' vend' pstart
>                      isb
>     where vstart' = VPtr $ fromPPtr $ ptrFromPAddr pstart
>           vend' = vstart' + (vend - vstart)
#else
> doFlush :: FlushType -> VPtr -> VPtr -> PAddr -> MachineMonad ()
> doFlush Clean vstart vend pstart =
>     cleanCacheRange_RAM vstart vend pstart
> doFlush Invalidate vstart vend pstart =
>     invalidateCacheRange_RAM vstart vend pstart
> doFlush CleanInvalidate vstart vend pstart =
>     cleanInvalidateCacheRange_RAM vstart vend pstart
> doFlush Unify vstart vend pstart = do
>     cleanCacheRange_PoU vstart vend pstart
>     dsb
>     invalidateCacheRange_I vstart vend pstart
>     branchFlushRange vstart vend pstart
>     isb
#endif

> flushPage :: VMPageSize -> PPtr PDE -> ASID -> VPtr -> Kernel ()
> flushPage _ pd asid vptr = do
>     assert (vptr .&. mask pageBits == 0)
>         "vptr must be 4k aligned"
>     root_switched <- setVMRootForFlush pd asid
>     maybe_hw_asid <- loadHWASID asid
>     when (isJust maybe_hw_asid) $ do
>       let Just hw_asid = maybe_hw_asid
>       doMachineOp $ invalidateLocalTLB_VAASID (fromVPtr vptr .|. (fromIntegral $ fromHWASID hw_asid))
>       when root_switched $ do
>           tcb <- getCurThread
>           setVMRoot tcb

> flushTable :: PPtr PDE -> ASID -> VPtr -> Kernel ()
> flushTable pd asid vptr = do
>     assert (vptr .&. mask (pageBitsForSize ARMSection) == 0)
>         "vptr must be 1MB aligned"
>     root_switched <- setVMRootForFlush pd asid
>     maybe_hw_asid <- loadHWASID asid
>     when (isJust maybe_hw_asid) $ do
>       doMachineOp $ invalidateLocalTLB_ASID (fromJust maybe_hw_asid)
>       when root_switched $ do
>           tcb <- getCurThread
>           setVMRoot tcb

> flushSpace :: ASID -> Kernel ()
> flushSpace asid = do
>     maybe_hw_asid <- loadHWASID asid
>     doMachineOp cleanCaches_PoU
>     case maybe_hw_asid of
>         Nothing -> return ()
>         Just hw_asid -> do
>             doMachineOp $ invalidateLocalTLB_ASID hw_asid

> invalidateTLBByASID :: ASID -> Kernel ()
> invalidateTLBByASID asid = do
>     maybe_hw_asid <- loadHWASID asid
>     case maybe_hw_asid of
>         Nothing -> return ()
>         Just hw_asid -> do
>             doMachineOp $ invalidateLocalTLB_ASID hw_asid

\subsection{Decoding ARM Invocations}

> labelToFlushType :: Word -> FlushType
> labelToFlushType label = case invocationType label of
>       ArchInvocationLabel ARMPDClean_Data -> Clean
>       ArchInvocationLabel ARMPageClean_Data -> Clean
>       ArchInvocationLabel ARMPDInvalidate_Data -> Invalidate
>       ArchInvocationLabel ARMPageInvalidate_Data -> Invalidate
>       ArchInvocationLabel ARMPDCleanInvalidate_Data -> CleanInvalidate
>       ArchInvocationLabel ARMPageCleanInvalidate_Data -> CleanInvalidate
>       ArchInvocationLabel ARMPDUnify_Instruction -> Unify
>       ArchInvocationLabel ARMPageUnify_Instruction -> Unify
>       _ -> error "Should never be called without a flush invocation"

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> pageBase :: (Num a, Bits a) => a -> VMPageSize -> a
> pageBase vaddr size = vaddr .&. (complement $ mask (pageBitsForSize size))
#else
> pageBase :: VPtr -> VMPageSize -> VPtr
> pageBase vaddr size = vaddr .&. (complement $ mask (pageBitsForSize size))
#endif

> resolveVAddr :: PPtr PDE -> VPtr -> Kernel (Maybe (VMPageSize, PAddr))
> resolveVAddr pd vaddr = do
>     let pdSlot = lookupPDSlot pd vaddr
>     pde <- getObject pdSlot
>     case pde of
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>         SectionPDE frame _ _ _ -> return $ Just (ARMSection, frame)
>         SuperSectionPDE frame _ _ _ -> return $ Just (ARMSuperSection, pageBase frame ARMSuperSection)
>         PageTablePDE table -> do
#else
>         SectionPDE frame _ _ _ _ _ _ -> return $ Just (ARMSection, frame)
>         SuperSectionPDE frame _ _ _ _ _ -> return $ Just (ARMSuperSection, frame)
>         PageTablePDE table _ _ -> do
#endif
>             let pt = ptrFromPAddr table
>             pteSlot <- lookupPTSlotFromPT pt vaddr
>             pte <- getObject pteSlot
>             case pte of
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>                 LargePagePTE frame _ _ _ -> return $ Just (ARMLargePage, pageBase frame ARMLargePage)
>                 SmallPagePTE frame _ _ _ -> return $ Just (ARMSmallPage, frame)
#else
>                 LargePagePTE frame _ _ _ _ -> return $ Just (ARMLargePage, frame)
>                 SmallPagePTE frame _ _ _ _ -> return $ Just (ARMSmallPage, frame)
#endif
>                 _ -> return Nothing
>         _ -> return Nothing

FIXME ARMHYP implement after decision re PageCap contents and MOVE

#ifdef CONFIG_ARM_SMMU
> isIOSpaceFrameCap :: ArchCapability -> Bool
> isIOSpaceFrameCap (PageCap {}) = error "FIXME ARMHYP undecided on PageCap contents"
> isIOSpaceFrameCap _ = error "isIOSpaceFrameCap: not a frame/page cap"
#endif

> decodeARMMMUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation

There are five ARM-specific capability types. They correspond to the two levels of the hardware-defined page table, the two levels of the global ASID table, and the frames used to back virtual memory pages.

Capabilities for page directories --- the top level of the hardware-defined page table --- have only a single invocation, which allows the user to clean and/or invalidate caches.

> decodeARMMMUInvocation label args _ _ cap@(PageDirectoryCap {}) _ =
>     case (isPDFlushLabel (invocationType label), args) of
>         (True, start:end:_) -> do
>             when (end <= start) $
>                 throw $ InvalidArgument 1
>             when (VPtr start >= pptrBase || VPtr end > pptrBase) $
>                 throw IllegalOperation
>             (pd,asid) <- case cap of
>                 PageDirectoryCap {
>                          capPDMappedASID = Just asid,
>                          capPDBasePtr = pd}
>                     -> return (pd,asid)
>                 _ -> throw $ InvalidCapability 0
>             pdCheck <- lookupErrorOnFailure False $ findPDForASID asid
>             when (pdCheck /= pd) $ throw $ InvalidCapability 0
>             frameInfo <-
>                  withoutFailure $ resolveVAddr (capPDBasePtr cap) (VPtr start)
>             case frameInfo of
>                 -- Fail if there is nothing mapped here
>                 Nothing -> return $ InvokePageDirectory PageDirectoryNothing
>                 Just frameInfo -> do
>                     withoutFailure $ checkValidMappingSize (fst frameInfo)
>                     let baseStart = pageBase (VPtr start) (fst frameInfo)
>                     let baseEnd = pageBase (VPtr end - 1) (fst frameInfo)
>                     when (baseStart /= baseEnd) $
>                         throw $ RangeError start $ fromVPtr $ baseStart +
>                                   mask (pageBitsForSize (fst frameInfo))
>                     let offset = start .&. mask (pageBitsForSize (fst frameInfo))
>                     let pStart = snd frameInfo + toPAddr offset
>                     return $ InvokePageDirectory $ PageDirectoryFlush {
>                          pdFlushType = labelToFlushType label,
>                          pdFlushStart = VPtr start,
>                          pdFlushEnd = VPtr end - 1,
>                          pdFlushPStart = pStart,
>                          pdFlushPD = pd,
>                          pdFlushASID = asid }
>         (True, _) -> throw TruncatedMessage
>         _ -> throw IllegalOperation

Capabilities for page tables --- that is, the second level of the hardware-defined page table structure --- have one method. It is used to attach the table to a top-level page directory, at a specific virtual address. It is a single-use method; if it succeeds, the table cannot be mapped again at a different address or in a different page directory, even if the original page directory is deleted. The mapping may only be removed by deleting the page table capability.

Note that these capabilities cannot be copied until they have been mapped, so any given page table object can only appear in one page directory. This is to ensure that the page unmapping operation always succeeds.

> decodeARMMMUInvocation label args _ cte cap@(PageTableCap {}) extraCaps =
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel ARMPageTableMap, vaddr:attr:_, (pdCap,_):_) -> do
>             when (isJust $ capPTMappedAddress cap) $
>                 throw $ InvalidCapability 0
>             (pd,asid) <- case pdCap of
>                 ArchObjectCap (PageDirectoryCap {
>                          capPDMappedASID = Just asid,
>                          capPDBasePtr = pd })
>                     -> return (pd,asid)
>                 _ -> throw $ InvalidCapability 1
>             when (VPtr vaddr >= pptrBase) $
>                 throw $ InvalidArgument 0
>             pdCheck <- lookupErrorOnFailure False $ findPDForASID asid
>             when (pdCheck /= pd) $ throw $ InvalidCapability 1
>             let pdIndex = vaddr `shiftR` (pageBits + ptBits - pteBits)
>             let vaddr' = pdIndex `shiftL` (pageBits + ptBits - pteBits)
>             let pdSlot = pd + (PPtr $ pdIndex `shiftL` pdeBits)
>             oldpde <- withoutFailure $ getObject pdSlot
>             unless (oldpde == InvalidPDE) $ throw DeleteFirst
>             let pde = PageTablePDE {
>                     pdeTable = addrFromPPtr $ capPTBasePtr cap
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>                     ,pdeParity = armParityEnabled $ attribsFromWord attr
>                     ,pdeDomain = 0
#endif
>                     }
>             return $ InvokePageTable $ PageTableMap {
>                 ptMapCap = ArchObjectCap $
>                     cap { capPTMappedAddress = Just (asid, VPtr vaddr') },
>                 ptMapCTSlot = cte,
>                 ptMapPDE = pde,
>                 ptMapPDSlot = pdSlot }
>         (ArchInvocationLabel ARMPageTableMap, _, _) -> throw TruncatedMessage
>         (ArchInvocationLabel ARMPageTableUnmap, _, _) -> do
>             cteVal <- withoutFailure $ getCTE cte
>             final <- withoutFailure $ isFinalCapability cteVal
>             unless final $ throw RevokeFirst
>             return $ InvokePageTable $ PageTableUnmap {
>                 ptUnmapCap = cap,
>                 ptUnmapCapSlot = cte }
>         _ -> throw IllegalOperation

Virtual page capabilities may each represent a single mapping into a page table. Unlike page table capabilities, they may be unmapped without deletion, and may be freely copied to allow multiple mappings of the same page. There are two operations \emph{Map} and \emph{Unmap} which affect the mapping of a page capability. In addition, \emph{Map} has a remapping mode which is used to change the access permissions on an existing mapping.

FIXME ARMHYP_SMMU check SMMU isIOSpaceFrameCap(cap) for unmap
FIXME ARMHYP TODO add call to ARMPageMapIO decode for map and unmap
FIXME ARMHYP capVPMappedAddress is not what we want for ARM\_HYP? C code has capFMappedAddress for ARM, capFBasePtr for ARM\_HYP here

> decodeARMMMUInvocation label args _ cte cap@(PageCap {}) extraCaps =
>  do
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel ARMPageMap, vaddr:rightsMask:attr:_, (pdCap,_):_) -> do
>             (pd,asid) <- case pdCap of
>                 ArchObjectCap (PageDirectoryCap {
>                         capPDMappedASID = Just asid,
>                         capPDBasePtr = pd })
>                     -> return (pd,asid)
>                 _ -> throw $ InvalidCapability 1
>             case capVPMappedAddress cap of
>                 Just (asid', vaddr') -> do
>                     when (asid' /= asid) $ throw $ InvalidCapability 1
>                     when (vaddr' /= (VPtr vaddr)) $ throw $ InvalidArgument 0
>                 Nothing ->  do
>                     let vtop = vaddr + bit (pageBitsForSize $ capVPSize cap) - 1
>                     when (VPtr vtop >= pptrBase) $ throw $ InvalidArgument 0
>             pdCheck <- lookupErrorOnFailure False $ findPDForASID asid
>             when (pdCheck /= pd) $ throw $ InvalidCapability 1
>             let vmRights = maskVMRights (capVPRights cap) $
>                     rightsFromWord rightsMask
>             checkVPAlignment (capVPSize cap) (VPtr vaddr)
>             entries <- createMappingEntries (addrFromPPtr $ capVPBasePtr cap)
>                 (VPtr vaddr) (capVPSize cap) vmRights
>                 (attribsFromWord attr) pd
>             ensureSafeMapping entries
>             return $ InvokePage $ PageMap {
>                 pageMapASID = asid,
>                 pageMapCap = ArchObjectCap $
>                     cap { capVPMappedAddress = Just (asid, VPtr vaddr) },
>                 pageMapCTSlot = cte,
>                 pageMapEntries = entries }
>         (ArchInvocationLabel ARMPageMap, _, _) -> throw TruncatedMessage
#ifdef CONFIG_ARM_SMMU
>         (ArchInvocationLabel ARMPageMapIO, _, _) -> error "FIXME ARMHYP_SMMU"
#endif
>         (ArchInvocationLabel ARMPageUnmap, _, _) ->
>                 return $
#ifdef CONFIG_ARM_SMMU
>                          if (isIOSpaceFrameCap cap)
>                          then error "FIXME ARMHYP_SMMU"
>                          else
#endif
>                               InvokePage $ PageUnmap {
>                                              pageUnmapCap = cap,
>                                              pageUnmapCapSlot = cte }
>         (ArchInvocationLabel ARMPageClean_Data, _, _) -> decodeARMPageFlush label args cap
>         (ArchInvocationLabel ARMPageInvalidate_Data, _, _) -> decodeARMPageFlush label args cap
>         (ArchInvocationLabel ARMPageCleanInvalidate_Data, _, _) -> decodeARMPageFlush label args cap
>         (ArchInvocationLabel ARMPageUnify_Instruction, _, _) -> decodeARMPageFlush label args cap
>         (ArchInvocationLabel ARMPageGetAddress, _, _) -> return $ InvokePage $ PageGetAddr (capVPBasePtr cap)
>         _ -> throw IllegalOperation

The ASID control capability refers to the top level of a global two-level table used for allocating address space identifiers. It has only one method, "MakePool", which creates an ASID allocation pool given a single frame of untyped memory. Since this method allocates part of a global range of ASIDs, it may return a "DeleteFirst" error if the entire range has been allocated to existing ASID pools.

> decodeARMMMUInvocation label args _ _ ASIDControlCap extraCaps =
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel ARMASIDControlMakePool, index:depth:_,
>                 (untyped,parentSlot):(croot,_):_) -> do
>             asidTable <- withoutFailure $ gets (armKSASIDTable . ksArchState)
>             let free = filter (\(x,y) -> x <= (bit asidHighBits) - 1 && isNothing y) $ assocs asidTable
>             when (null free) $ throw DeleteFirst
>             let base = (fst $ head free) `shiftL` asidLowBits
>             let pool = makeObject :: ASIDPool
>             frame <- case untyped of
>                 UntypedCap {capIsDevice = False} | capBlockSize untyped == objBits pool -> do
>                     ensureNoChildren parentSlot
>                     return $ capPtr untyped
>                 _ -> throw $ InvalidCapability 1
>             destSlot <- lookupTargetSlot
>                 croot (CPtr index) (fromIntegral depth)
>             ensureEmptySlot destSlot
>             return $ InvokeASIDControl $ MakePool {
>                 makePoolFrame = frame,
>                 makePoolSlot = destSlot,
>                 makePoolParent = parentSlot,
>                 makePoolBase = base }
>         (ArchInvocationLabel ARMASIDControlMakePool, _, _) -> throw TruncatedMessage
>         _ -> throw IllegalOperation

ASID pool capabilities are used to allocate unique address space identifiers for virtual address spaces. They support the "Assign" method, which allocates an ASID for a given page directory capability. The directory must not already have an ASID. Page directories cannot be used until they have been allocated an ASID using this method.

> decodeARMMMUInvocation label _ _ _ cap@(ASIDPoolCap {}) extraCaps =
>     case (invocationType label, extraCaps) of
>         (ArchInvocationLabel ARMASIDPoolAssign, (pdCap,pdCapSlot):_) ->
>             case pdCap of
>                 ArchObjectCap (PageDirectoryCap { capPDMappedASID = Nothing })
>                   -> do
>                     asidTable <- withoutFailure $ gets (armKSASIDTable . ksArchState)
>                     let base = capASIDBase cap
>                     let poolPtr = asidTable!(asidHighBitsOf base)
>                     when (isNothing poolPtr) $ throw $ FailedLookup False InvalidRoot
>                     let Just p = poolPtr
>                     when (p /= capASIDPool cap) $ throw $ InvalidCapability 0
>                     ASIDPool pool <- withoutFailure $ getObject $ p
>                     let free = filter (\(x,y) -> x <=  (bit asidLowBits) - 1
>                                                  && x + base /= 0 && isNothing y) $ assocs pool
>                     when (null free) $ throw DeleteFirst
>                     let asid = fst $ head free
>                     return $ InvokeASIDPool $ Assign {
>                         assignASID = asid + base,
>                         assignASIDPool = capASIDPool cap,
>                         assignASIDCTSlot = pdCapSlot }
>                 _ -> throw $ InvalidCapability 1
>         (ArchInvocationLabel ARMASIDPoolAssign, _) -> throw TruncatedMessage
>         _ -> throw IllegalOperation

The function should not be called on any other cap types.

> decodeARMMMUInvocation _ _ _ _ _ _ = fail "decodeARMMMUInvocation: not an MMU invocation"


> decodeARMPageFlush :: Word -> [Word] -> ArchCapability ->
>                       KernelF SyscallError ArchInv.Invocation
> decodeARMPageFlush label args cap = case (args, capVPMappedAddress cap) of
>     (start:end:_, Just (asid, vaddr)) -> do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>         let vaddr' = capVPBasePtr cap
#endif
>         pd <- lookupErrorOnFailure False $ findPDForASID asid
>         when (end <= start) $
>             throw $ InvalidArgument 1
>         let pageSize = bit (pageBitsForSize (capVPSize cap))
>         let pageBase = addrFromPPtr $ capVPBasePtr cap
>         when (start >= pageSize || end > pageSize) $
>             throw $ InvalidArgument 0
>         let pstart = pageBase + toPAddr start
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>         let start' = start + fromPPtr vaddr'
>         let end' = end + fromPPtr vaddr'
>         when (pstart < paddrBase || ((end' - start') + fromPAddr pstart > fromPAddr paddrTop)) $
>             throw IllegalOperation
#else
>         let start' = start + fromVPtr vaddr
>         let end' = end + fromVPtr vaddr
#endif
>         return $ InvokePage $ PageFlush {
>               pageFlushType = labelToFlushType label,
>               pageFlushStart = VPtr $ start',
>               pageFlushEnd = VPtr $ end' - 1,
>               pageFlushPStart = pstart,
>               pageFlushPD = pd,
>               pageFlushASID = asid }
>     (_:_:_, Nothing) -> throw IllegalOperation
>     _ -> throw TruncatedMessage

Checking virtual address for page size dependent alignment:

> checkVPAlignment :: VMPageSize -> VPtr -> KernelF SyscallError ()
>
> checkVPAlignment sz w =
>     unless (w .&. mask (pageBitsForSize sz) == 0) $
>            throw AlignmentError

When we fetch a mapping in which to perform a page flush, we assert that its
size is valid. This check is ignored in Haskell, but the Isabelle model has a
notion of the largest permitted object size, and checks it appropriately.

> checkValidMappingSize :: VMPageSize -> Kernel ()
> checkValidMappingSize _ = return ()

\subsection{Invocation Implementations}

> performARMMMUInvocation :: ArchInv.Invocation -> KernelP [Word]
> performARMMMUInvocation i = withoutPreemption $ do
>     case i of
>         InvokePageDirectory oper -> do
>             performPageDirectoryInvocation oper
>             return []
>         InvokePageTable oper -> do
>             performPageTableInvocation oper
>             return []
>         InvokePage oper -> performPageInvocation oper
>         InvokeASIDControl oper -> do
>             performASIDControlInvocation oper
>             return []
>         InvokeASIDPool oper -> do
>             performASIDPoolInvocation oper
>             return []
>         _ -> fail "performARMMMUInvocation: not an MMU invocation"

> performPageDirectoryInvocation :: PageDirectoryInvocation -> Kernel ()
> performPageDirectoryInvocation (PageDirectoryFlush typ start end pstart pd asid) =

Don't flush an empty range.

>     when (start < end) $ do
>         root_switched <- setVMRootForFlush pd asid
>         doMachineOp $ doFlush typ start end pstart
>         when root_switched $ do
>             tcb <- getCurThread
>             setVMRoot tcb

> performPageDirectoryInvocation PageDirectoryNothing = return ()

> performPageTableInvocation :: PageTableInvocation -> Kernel ()

> performPageTableInvocation (PageTableMap cap ctSlot pde pdSlot) = do
>     updateCap ctSlot cap
>     storePDE pdSlot pde
>     doMachineOp $ cleanByVA_PoU (VPtr $ fromPPtr $ pdSlot) (addrFromPPtr pdSlot)

> performPageTableInvocation (PageTableUnmap cap ctSlot) = do
>     case capPTMappedAddress cap of
>         Just (asid, vaddr) -> do
>             unmapPageTable asid vaddr (capPTBasePtr cap)
>             let ptr = capPTBasePtr cap
>             let slots = [ptr, ptr + bit pteBits .. ptr + bit ptBits - 1]
>             mapM_ (flip storePTE InvalidPTE) slots
>             doMachineOp $
>                 cleanCacheRange_PoU (VPtr $ fromPPtr $ ptr)
>                                     (VPtr $ fromPPtr $ (ptr + bit ptBits - 1))
>                                     (addrFromPPtr ptr)
>         Nothing -> return ()
>     ArchObjectCap cap <- getSlotCap ctSlot
>     updateCap ctSlot (ArchObjectCap $
>                            cap { capPTMappedAddress = Nothing })

When checking if there was already something mapped before a PageMap,
we need only check the first slot because ensureSafeMapping tells us that
the PT/PD is consistent.

> pteCheckIfMapped :: PPtr PTE -> Kernel Bool
> pteCheckIfMapped slot = do
>     pt <- getObject slot
>     return $ pt /= InvalidPTE

> pdeCheckIfMapped :: PPtr PDE -> Kernel Bool
> pdeCheckIfMapped slot = do
>     pd <- getObject slot
>     return $ pd /= InvalidPDE

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> addPTEOffset :: PTE -> Word -> PTE
> addPTEOffset pte i = if pte == InvalidPTE then InvalidPTE
>                      else pte { pteFrame = addPAddr (pteFrame pte)
>                                  (i * bit (pageBitsForSize(ARMSmallPage))) }

> addPDEOffset :: PDE -> Word -> PDE
> addPDEOffset InvalidPDE _ = InvalidPDE
> addPDEOffset (PageTablePDE p) _ = PageTablePDE p
> addPDEOffset pde i = pde { pdeFrame = addPAddr (pdeFrame pde)
>                                 (i * bit (pageBitsForSize(ARMSection))) }
#endif

> performPageInvocation :: PageInvocation -> Kernel [Word]
>
> performPageInvocation (PageMap asid cap ctSlot entries) = do
>     updateCap ctSlot cap
>     case entries of
>         Left (pte, slots) -> do
>             tlbFlush <- pteCheckIfMapped (head slots)
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>             mapM (\(slot, i) -> storePTE slot (addPTEOffset pte i))
>                  (zip slots [0 .. fromIntegral (length slots - 1)])
#else
>             mapM (flip storePTE pte) slots
#endif
>             doMachineOp $
>                 cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
>                                     (VPtr $ (fromPPtr (last slots)) + (bit pteBits - 1))
>                                     (addrFromPPtr (head slots))
>             when tlbFlush $ invalidateTLBByASID asid
>         Right (pde, slots) -> do
>             tlbFlush <- pdeCheckIfMapped (head slots)
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>             mapM (\(slot, i) -> storePDE slot (addPDEOffset pde i))
>                  (zip slots [0 .. fromIntegral (length slots - 1)])
#else
>             mapM (flip storePDE pde) slots
#endif
>             doMachineOp $
>                 cleanCacheRange_PoU (VPtr $ fromPPtr $ head slots)
>                                     (VPtr $ (fromPPtr (last slots)) + (bit pdeBits - 1))
>                                     (addrFromPPtr (head slots))
>             when tlbFlush $ invalidateTLBByASID asid
>     return []
>
> performPageInvocation (PageUnmap cap ctSlot) = do
>     case capVPMappedAddress cap of
>         Just (asid, vaddr) -> unmapPage (capVPSize cap) asid vaddr
>                                     (capVPBasePtr cap)
>         Nothing -> return ()
>     ArchObjectCap cap <- getSlotCap ctSlot
>     updateCap ctSlot (ArchObjectCap $
>                            cap { capVPMappedAddress = Nothing })
>     return []
>
> performPageInvocation (PageFlush typ start end pstart pd asid) = do
>     when (start < end) $ do
>         root_switched <- setVMRootForFlush pd asid
>         doMachineOp $ doFlush typ start end pstart
>         when root_switched $ do
>             tcb <- getCurThread
>             setVMRoot tcb
>     return []
>
> performPageInvocation (PageGetAddr ptr) = do
>     return [fromPAddr $ addrFromPPtr ptr]

> performASIDControlInvocation :: ASIDControlInvocation -> Kernel ()
> performASIDControlInvocation (MakePool frame slot parent base) = do
>     deleteObjects frame pageBits
>     pcap <- getSlotCap parent
>     updateFreeIndex parent (maxFreeIndex (capBlockSize pcap))
>     placeNewObject frame (makeObject :: ASIDPool) 0
>     let poolPtr = PPtr $ fromPPtr frame
>     cteInsert (ArchObjectCap $ ASIDPoolCap poolPtr base) parent slot
>     assert (base .&. mask asidLowBits == 0)
>         "ASID pool's base must be aligned"
>     asidTable <- gets (armKSASIDTable . ksArchState)
>     let asidTable' = asidTable//[(asidHighBitsOf base, Just poolPtr)]
>     modify (\s -> s {
>         ksArchState = (ksArchState s) { armKSASIDTable = asidTable' }})

> performASIDPoolInvocation :: ASIDPoolInvocation -> Kernel ()
> performASIDPoolInvocation (Assign asid poolPtr ctSlot) = do
>     oldcap <- getSlotCap ctSlot
>     ASIDPool pool <- getObject poolPtr
>     let ArchObjectCap cap = oldcap
>     updateCap ctSlot (ArchObjectCap $ cap { capPDMappedASID = Just asid })
>     let pool' = pool//[(asid .&. mask asidLowBits, Just $ capPDBasePtr cap)]
>     setObject poolPtr $ ASIDPool pool'

\subsection{Simulator Support}

The kernel model's ARM targets use an external simulation of the physical address space for user-level virtual memory, I/O devices and MMU data structures, separate from the "PSpace" which is used for kernel objects. However, "PDE" objects are accessed by the kernel, so they must be stored in both the external physical memory model and the internal "PSpace". To make verification simpler we do the same for "PTE" objects.

> storePDE :: PPtr PDE -> PDE -> Kernel ()
> storePDE slot pde = do
>     setObject slot pde
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPDE pde
#else
>     let [w0, w1] = wordsFromPDE pde
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) w0
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot + fromIntegral wordSize) w1
#endif

> storePTE :: PPtr PTE -> PTE -> Kernel ()
> storePTE slot pte = do
>     setObject slot pte
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPTE pte
#else
>     let [w0, w1] = wordsFromPTE pte
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) w0
>     doMachineOp $ storeWordVM (PPtr $ fromPPtr slot + fromIntegral wordSize) w1
#endif

FIXME ARMHYP IOPTE IOPDE - here or in IOSpace?

