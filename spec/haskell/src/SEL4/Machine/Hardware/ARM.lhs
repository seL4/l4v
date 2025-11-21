%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

\begin{impdetails}

> {-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

\end{impdetails}

This module defines the low-level ARM hardware interface.

> module SEL4.Machine.Hardware.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine.RegisterSet

> import Control.Monad.Reader
> import Data.Bits
> import Data.Word(Word8, Word32, Word64)
> import Data.Ix

\end{impdetails}

The ARM-specific register set definitions are qualified with the "ARM" prefix, and the platform-specific hardware access functions are qualified with the "Platform" prefix. The latter module is outside the scope of the reference manual; for the executable model, it is specific to the external simulator used for user-level code.

> import qualified SEL4.Machine.RegisterSet.TARGET as ARM
> import qualified SEL4.Machine.Hardware.TARGET.Callbacks as Platform
> import qualified SEL4.Machine.Hardware.TARGET.PLATFORM as Platform

\subsection{Data Types}

The machine monad contains a platform-specific opaque pointer, used by the external simulator interface.

> type MachineData = Platform.MachineData

> type MachineMonad = ReaderT MachineData IO

> type IRQ = Platform.IRQ

> newtype HardwareASID = HardwareASID { fromHWASID :: Word8 }
>     deriving (Num, Enum, Bounded, Ord, Ix, Eq, Show)

> toPAddr = Platform.PAddr

\subsubsection{Virtual Memory}

ARM hardware-defined pages come in four sizes: 4k, 64k, 1M and 16M. The 16M page size only has hardware support on some ARMv6 CPUs, such as the ARM1136; the kernel will simulate them using 16 1M mappings on other CPUs.

> data VMPageSize
>     = ARMSmallPage
>     | ARMLargePage
>     | ARMSection
>     | ARMSuperSection
>     deriving (Show, Eq, Ord, Enum, Bounded)

ARM virtual memory faults are handled by one of two trap handlers: one for data aborts, and one for instruction aborts.

> data VMFaultType
>     = ARMDataAbort
>     | ARMPrefetchAbort
>     deriving Show

\subsection{Hypervisor}

> data HypFaultType
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     = ARMVCPUFault Word32 -- HSR
#else
>     = ARMNoHypFaults
#endif
>     deriving Show

\subsubsection{Physical Memory}

The ARM MMU does not allow access to physical addresses while translation is enabled; the kernel must access its objects via virtual addresses. Depending on the platform, these virtual addresses may either be the same as the physical addresses, or offset by a constant.

> type PAddr = Platform.PAddr

> fromPAddr :: PAddr -> Word
> fromPAddr = Platform.fromPAddr

> paddrBase :: PAddr
> paddrBase = Platform.physBase

> pptrBase :: VPtr
> pptrBase = Platform.pptrBase

> pptrTop :: VPtr
> pptrTop = VPtr 0xfff00000

> paddrTop :: PAddr
> paddrTop = toPAddr $ (fromVPtr pptrTop - pptrBaseOffset)

> kernelELFPAddrBase :: PAddr
> kernelELFPAddrBase = paddrBase

> kernelELFBase :: VPtr
> kernelELFBase = VPtr $ fromVPtr pptrBase + (fromPAddr kernelELFPAddrBase .&. (mask 22))

> pptrBaseOffset = (fromVPtr pptrBase) - (fromPAddr paddrBase)

> ptrFromPAddr :: PAddr -> PPtr a
> ptrFromPAddr addr = PPtr $ fromPAddr addr + pptrBaseOffset

> addrFromPPtr :: PPtr a -> PAddr
> addrFromPPtr addr = toPAddr $ fromPPtr addr - pptrBaseOffset

> kernelELFBaseOffset = (fromVPtr kernelELFBase) - (fromPAddr kernelELFPAddrBase)

> addrFromKPPtr :: PPtr a -> PAddr
> addrFromKPPtr (PPtr addr) = toPAddr $ addr - kernelELFBaseOffset

> addPAddr :: PAddr -> Word -> PAddr
> addPAddr p w = toPAddr (fromPAddr p + w)

\subsection{Hardware Access}

The following functions define the ARM-specific interface between the kernel and the hardware. Most of them depend on the simulator in use, and are therefore defined in the platform module.

> pageBits :: Int
> pageBits = 12

> pageBitsForSize :: VMPageSize -> Int
> pageBitsForSize ARMSmallPage = 12
> pageBitsForSize ARMLargePage = 16
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
> pageBitsForSize ARMSection = 20
> pageBitsForSize ARMSuperSection = 24
#else
> pageBitsForSize ARMSection = 21
> pageBitsForSize ARMSuperSection = 25
#endif

> getMemoryRegions :: MachineMonad [(PAddr, PAddr)]
> getMemoryRegions = do
>     cpbtr <- ask
>     liftIO $ Platform.getMemoryRegions cpbtr

> getDeviceRegions :: MachineMonad [(PAddr, PAddr)]
> getDeviceRegions = do
>     cbptr <- ask
>     liftIO $ Platform.getDeviceRegions cbptr

> getKernelDevices :: MachineMonad [(PAddr, PPtr Word)]
> getKernelDevices = do
>     cbptr <- ask
>     liftIO $ Platform.getKernelDevices cbptr

> loadWord :: PPtr Word -> MachineMonad Word
> loadWord ptr = do
>     cbptr <- ask
>     liftIO $ Platform.loadWordCallback cbptr $ addrFromPPtr ptr

> storeWord :: PPtr Word -> Word -> MachineMonad ()
> storeWord ptr val = do
>     cbptr <- ask
>     liftIO $ Platform.storeWordCallback cbptr (addrFromPPtr ptr) val

> storeWordVM :: PPtr Word -> Word -> MachineMonad ()
> storeWordVM ptr val = storeWord ptr val

> pageColourBits :: Int
> pageColourBits = Platform.pageColourBits

> getActiveIRQ :: Bool -> MachineMonad (Maybe IRQ)
> getActiveIRQ _ = do
>     cbptr <- ask
>     liftIO $ Platform.getActiveIRQ cbptr

> ackInterrupt :: IRQ -> MachineMonad ()
> ackInterrupt irq = do
>     cbptr <- ask
>     liftIO $ Platform.ackInterrupt cbptr irq

> maskInterrupt :: Bool -> IRQ -> MachineMonad ()
> maskInterrupt maskI irq = do
>     cbptr <- ask
>     liftIO $ Platform.maskInterrupt cbptr maskI irq

> deactivateInterrupt :: IRQ -> MachineMonad ()
> deactivateInterrupt irq = error "Unimplemented - GICv3 machine op"

> configureTimer :: MachineMonad IRQ
> configureTimer = do
>     cbptr <- ask
>     liftIO $ Platform.configureTimer cbptr

> initIRQController :: MachineMonad ()
> initIRQController = do
>     cbptr <- ask
>     liftIO $ Platform.initIRQController cbptr

> setIRQTrigger :: IRQ -> Bool -> MachineMonad ()
> setIRQTrigger irq trigger = error "ARM machine callback unimplemented"

> handleSpuriousIRQ_mop :: MachineMonad ()
> handleSpuriousIRQ_mop = error "See MachineOps.thy"

> resetTimer :: MachineMonad ()
> resetTimer = do
>     cbptr <- ask
>     liftIO $ Platform.resetTimer cbptr

> debugPrint :: String -> MachineMonad ()
> debugPrint str = liftIO $ putStrLn str

> getRestartPC = getRegister (Register ARM.FaultIP)
> setNextPC = setRegister (Register ARM.NextIP)

> getTPIDRURW :: MachineMonad Word
> getTPIDRURW = error "machine callback unimplemented"

> setTPIDRURW :: Word -> MachineMonad ()
> setTPIDRURW = error "machine callback unimplemented"

\subsection{ARM Memory Management}

There are several operations used by the ARM memory management code to access relevant hardware registers.

\subsubsection{Cleaning Memory}

This function is called before a region of user-memory is recycled.
It zeros every word to ensure that user tasks cannot access any private data
that might previously have been stored in the region and
then flushes the kernel's mapping from the virtually-indexed caches.

> clearMemory :: PPtr Word -> Int -> MachineMonad ()
> clearMemory ptr byteLength = do
>     let wordSize = fromIntegral $ finiteBitSize (undefined::Word) `div` 8
>     let ptr' = PPtr $ fromPPtr ptr
>     let ptrs = [ptr', ptr' + wordSize .. ptr' + fromIntegral byteLength - 1]
>     mapM_ (\p -> storeWord p 0) ptrs
>     cleanCacheRange_PoU (VPtr $ fromPPtr ptr)
>                         (VPtr (fromPPtr (ptr + fromIntegral byteLength - 1)))
>                         (toPAddr $ fromPPtr ptr)

This function is called before a region of memory is made user-accessible.
Though in Haskell, it is implemented as "clearMemory",
we draw the logical distinction to gain more freedom for its interpretation
in the Isabelle formalization.

> initMemory :: PPtr Word -> Int -> MachineMonad ()
> initMemory = clearMemory

This function is called to free a region of user-memory after use.
In Haskell, this operation does not do anything.
We just use it as a stub for the Isabelle formalization.

> freeMemory :: PPtr Word -> Int -> MachineMonad ()
> freeMemory _ _ = return ()

Same as "clearMemory", but uses storeWordVM to write to memory.
To be used when creating mapping objects (page tables and -dirs)
Flushing the kernel's mapping from the virtually-indexed
caches must be done separately.

> clearMemoryVM :: PPtr Word -> Int -> MachineMonad ()
> clearMemoryVM ptr bits = do
>     let wordSize = fromIntegral $ finiteBitSize (undefined::Word) `div` 8
>     let ptr' = PPtr $ fromPPtr ptr
>     let ptrs = [ptr', ptr' + wordSize .. ptr' + 1 `shiftL` bits - 1]
>     mapM_ (\p -> storeWordVM p 0) ptrs

\subsubsection{Address Space Setup}

> writeTTBR0 :: Word -> MachineMonad ()
> writeTTBR0 w = do
>     cbptr <- ask
>     liftIO $ Platform.writeTTBR0 cbptr w

> writeTTBR0Ptr :: PAddr -> MachineMonad ()
> writeTTBR0Ptr pd = writeTTBR0 ((fromPAddr pd .&. 0xffffe000) .|. 0x18)

> setCurrentPD :: PAddr -> MachineMonad ()
> setCurrentPD pd = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     setCurrentPDPL2 pd
#else
>     dsb
>     writeTTBR0Ptr pd
>     isb
#endif

> setHardwareASID :: HardwareASID -> MachineMonad ()
> setHardwareASID (HardwareASID hw_asid) = do
>     cbptr <- ask
>     liftIO $ Platform.setHardwareASID cbptr hw_asid

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

> setCurrentPDPL2 :: PAddr -> MachineMonad ()
> setCurrentPDPL2 = error "FIXME ARMHYP machine callback unimplemented"

> writeContextIDAndPD :: HardwareASID -> PAddr -> MachineMonad ()
> writeContextIDAndPD = error "FIXME ARMHYP  machine callback unimplemented"

> getTPIDRURO :: MachineMonad Word
> getTPIDRURO = error "FIXME ARMHYP machine callback unimplemented"

> setTPIDRURO :: Word -> MachineMonad ()
> setTPIDRURO = error "FIXME ARMHYP machine callback unimplemented"

#endif

\subsubsection{Memory Barriers}

> isb :: MachineMonad ()
> isb = do
>     cbptr <- ask
>     liftIO $ Platform.isbCallback cbptr

> dsb :: MachineMonad ()
> dsb = do
>     cbptr <- ask
>     liftIO $ Platform.dsbCallback cbptr

> dmb :: MachineMonad ()
> dmb = do
>     cbptr <- ask
>     liftIO $ Platform.dmbCallback cbptr

\subsubsection{Cache Cleaning and TLB Flushes}

> invalidateLocalTLB :: MachineMonad ()
> invalidateLocalTLB = do
>     cbptr <- ask
>     liftIO $ Platform.invalidateLocalTLBCallback cbptr

> invalidateLocalTLB_ASID :: HardwareASID -> MachineMonad ()
> invalidateLocalTLB_ASID (HardwareASID hw_asid) = do
>     cbptr <- ask
>     liftIO $ Platform.invalidateLocalTLB_ASIDCallback cbptr hw_asid

> invalidateLocalTLB_VAASID :: Word -> MachineMonad ()
> invalidateLocalTLB_VAASID mva_plus_asid = do
>     cbptr <- ask
>     liftIO $ Platform.invalidateLocalTLB_VAASIDCallback cbptr mva_plus_asid

> cleanByVA :: VPtr -> PAddr -> MachineMonad ()
> cleanByVA mva pa = do
>     cbptr <- ask
>     liftIO $ Platform.cacheCleanByVACallback cbptr mva pa

> cleanByVA_PoU :: VPtr -> PAddr -> MachineMonad ()
> cleanByVA_PoU mva pa = do
>     cbptr <- ask
>     liftIO $ Platform.cacheCleanByVA_PoUCallback cbptr mva pa

> invalidateByVA :: VPtr -> PAddr -> MachineMonad ()
> invalidateByVA mva pa = do
>     cbptr <- ask
>     liftIO $ Platform.cacheInvalidateByVACallback cbptr mva pa

> invalidateByVA_I :: VPtr -> PAddr -> MachineMonad ()
> invalidateByVA_I mva pa = do
>     cbptr <- ask
>     liftIO $ Platform.cacheInvalidateByVA_ICallback cbptr mva pa

> invalidate_I_PoU :: MachineMonad ()
> invalidate_I_PoU = do
>     cbptr <- ask
>     liftIO $ Platform.cacheInvalidate_I_PoUCallback cbptr

> cleanInvalByVA :: VPtr -> PAddr -> MachineMonad ()
> cleanInvalByVA mva pa = do
>     cbptr <- ask
>     liftIO $ Platform.cacheCleanInvalidateByVACallback cbptr mva pa

> branchFlush :: VPtr -> PAddr -> MachineMonad ()
> branchFlush mva pa = do
>     cbptr <- ask
>     liftIO $ Platform.branchFlushCallback cbptr mva pa

> clean_D_PoU :: MachineMonad ()
> clean_D_PoU = do
>     cbptr <- ask
>     liftIO $ Platform.cacheClean_D_PoUCallback cbptr

> cleanInvalidate_D_PoC :: MachineMonad ()
> cleanInvalidate_D_PoC = do
>     cbptr <- ask
>     liftIO $ Platform.cacheCleanInvalidate_D_PoCCallback cbptr

> cleanInvalidate_D_PoU :: MachineMonad ()
> cleanInvalidate_D_PoU = do
>     cbptr <- ask
>     liftIO $ Platform.cacheCleanInvalidate_D_PoUCallback cbptr

> cleanInvalidateL2Range :: PAddr -> PAddr -> MachineMonad ()
> cleanInvalidateL2Range start end = do
>     cbptr <- ask
>     liftIO $ Platform.cacheCleanInvalidateL2RangeCallback cbptr start end

> invalidateL2Range :: PAddr -> PAddr -> MachineMonad ()
> invalidateL2Range start end = do
>     cbptr <- ask
>     liftIO $ Platform.cacheInvalidateL2RangeCallback cbptr start end

> cleanL2Range :: PAddr -> PAddr -> MachineMonad ()
> cleanL2Range start end = do
>     cbptr <- ask
>     liftIO $ Platform.cacheCleanL2RangeCallback cbptr start end

> lineStart addr = (addr `shiftR` cacheLineBits) `shiftL` cacheLineBits

Performs the given operation on every cache line that intersects the
supplied range.

> cacheRangeOp :: (VPtr -> PAddr -> MachineMonad ()) ->
>                 VPtr -> VPtr -> PAddr -> MachineMonad ()
> cacheRangeOp operation vstart vend pstart = do
>     let pend = pstart + (toPAddr $ fromVPtr (vend - vstart))
>     let vptrs = [lineStart vstart, lineStart vstart + fromIntegral cacheLine .. lineStart vend]
>     let pptrs = [lineStart pstart, lineStart pstart + fromIntegral cacheLine .. lineStart pend]
>     mapM_ (\(v,p) -> operation v p) (zip vptrs pptrs)

> cleanCacheRange_PoC :: VPtr -> VPtr -> PAddr -> MachineMonad ()
> cleanCacheRange_PoC vstart vend pstart =
>     cacheRangeOp cleanByVA vstart vend pstart

> cleanInvalidateCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
> cleanInvalidateCacheRange_RAM vstart vend pstart = do
>     cleanCacheRange_PoC vstart vend pstart
>     dsb
>     cleanInvalidateL2Range pstart (pstart + (toPAddr $ fromVPtr $ vend - vstart))
>     cacheRangeOp cleanInvalByVA vstart vend pstart
>     dsb

> cleanCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
> cleanCacheRange_RAM vstart vend pstart = do
>     cleanCacheRange_PoC vstart vend pstart
>     dsb
>     cleanL2Range pstart (pstart + (toPAddr $ fromVPtr $ vend - vstart))

> cleanCacheRange_PoU :: VPtr -> VPtr -> PAddr -> MachineMonad ()
> cleanCacheRange_PoU vstart vend pstart =
>     cacheRangeOp cleanByVA_PoU vstart vend pstart

> invalidateCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
> invalidateCacheRange_RAM vstart vend pstart = do
>     when (vstart /= lineStart vstart) $
>         cleanCacheRange_RAM vstart vstart pstart
>     when (vend + 1 /= lineStart (vend + 1)) $
>         cleanCacheRange_RAM (lineStart vend) (lineStart vend)
>             (pstart + (toPAddr $ fromVPtr $ lineStart vend - vstart))
>     invalidateL2Range pstart
>         (pstart + (toPAddr $ fromVPtr $ vend - vstart))
>     cacheRangeOp invalidateByVA vstart vend pstart
>     dsb

> invalidateCacheRange_I :: VPtr -> VPtr -> PAddr -> MachineMonad ()
> invalidateCacheRange_I vstart vend pstart =
>     cacheRangeOp invalidateByVA_I vstart vend pstart

> branchFlushRange :: VPtr -> VPtr -> PAddr -> MachineMonad ()
> branchFlushRange vstart vend pstart =
>     cacheRangeOp branchFlush vstart vend pstart

> cleanCaches_PoU :: MachineMonad ()
> cleanCaches_PoU = do
>     dsb
>     clean_D_PoU
>     dsb
>     invalidate_I_PoU
>     dsb

> cleanInvalidateL1Caches :: MachineMonad ()
> cleanInvalidateL1Caches = do
>     dsb
>     cleanInvalidate_D_PoC
>     dsb
>     invalidate_I_PoU
>     dsb

This function is used to clear the load exclusive monitor. This dummy
implementation assumes the monitor is not modelled in our simulator.

> clearExMonitor :: MachineMonad ()
> clearExMonitor = return ()

\subsubsection{Fault Status Registers}

> getIFSR :: MachineMonad Word
> getIFSR = do
>     cbptr <- ask
>     liftIO $ Platform.getIFSR cbptr

> getDFSR :: MachineMonad Word
> getDFSR = do
>     cbptr <- ask
>     liftIO $ Platform.getDFSR cbptr

> getFAR :: MachineMonad VPtr
> getFAR = do
>     cbptr <- ask
>     liftIO $ Platform.getFAR cbptr

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

\subsection{Hypervisor-specific status/control registers}

> getHSR :: MachineMonad Word
> getHSR = error "FIXME ARMHYP machine callback unimplemented"

> setHCR :: Word -> MachineMonad ()
> setHCR _hcr = error "FIXME ARMHYP machine callback unimplemented"

> getHDFAR :: MachineMonad VPtr
> getHDFAR = error "FIXME ARMHYP machine callback unimplemented"

> addressTranslateS1 :: VPtr -> MachineMonad VPtr
> addressTranslateS1 = error "FIXME ARMHYP machine callback unimplemented"

> getSCTLR :: MachineMonad Word
> getSCTLR = error "FIXME ARMHYP machine callback unimplemented"

> setSCTLR :: Word -> MachineMonad ()
> setSCTLR _sctlr = error "FIXME ARMHYP machine callback unimplemented"

\subsection{Hypervisor banked registers}

Rather than a line-for-line copy of every hypervisor register storage and
retrieval function from the C code, we abstract the concept into one function
each. Some special registers, like SCTLR, still get their own load/store
functions due to being operated on separately.

> readVCPUHardwareReg :: ARM.VCPUReg -> MachineMonad Word
> readVCPUHardwareReg reg = error "FIXME ARMHYP machine callback unimplemented"

> writeVCPUHardwareReg :: ARM.VCPUReg -> Word -> MachineMonad ()
> writeVCPUHardwareReg reg val = error "FIXME ARMHYP machine callback unimplemented"

#endif

\subsubsection{Page Table Structure}

The ARM architecture defines a two-level hardware-walked page table. The kernel must write entries to this table in the defined format to construct address spaces for user-level tasks.

#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT

The following types are Haskell representations of an entry in an ARMv6 page table. The "PDE" (page directory entry) type is an entry in the first level, and the "PTE" (page table entry) type is an entry in the second level. Note that "SuperSectionPDE" is an extension provided by some ARMv6 cores.

> data PDE
>     = InvalidPDE
>     | PageTablePDE {
>         pdeTable :: PAddr,
>         pdeParity :: Bool,
>         pdeDomain :: Word }
>     | SectionPDE {
>         pdeFrame :: PAddr,
>         pdeParity :: Bool,
>         pdeDomain :: Word,
>         pdeCacheable :: Bool,
>         pdeGlobal :: Bool,
>         pdeExecuteNever :: Bool,
>         pdeRights :: VMRights }
>     | SuperSectionPDE {
>         pdeFrame :: PAddr,
>         pdeParity :: Bool,
>         pdeCacheable :: Bool,
>         pdeGlobal :: Bool,
>         pdeExecuteNever :: Bool,
>         pdeRights :: VMRights }
>     deriving (Show, Eq)

> wordFromPDE :: PDE -> Word
> wordFromPDE InvalidPDE = 0
> wordFromPDE (PageTablePDE table parity domain) = 1 .|.
>     (fromIntegral table .&. 0xfffffc00) .|.
>     (if parity then bit 9 else 0) .|.
>     ((domain .&. 0xf) `shiftL` 5)
> wordFromPDE (SectionPDE frame parity domain cacheable global xn rights) = 2 .|.
>     (fromIntegral frame .&. 0xfff00000) .|.
>     (if parity then bit 9 else 0) .|.
>     (if cacheable then bit 2 .|. bit 3 else 0) .|.
>     (if xn then bit 4 else 0) .|.
>     ((domain .&. 0xf) `shiftL` 5) .|.
>     (if global then 0 else bit 17) .|.
>     (fromIntegral $ fromEnum rights `shiftL` 10)
> wordFromPDE (SuperSectionPDE frame parity cacheable global xn rights) = 2 .|.
>     bit 18 .|.
>     (fromIntegral frame .&. 0xff000000) .|.
>     (if parity then bit 9 else 0) .|.
>     (if cacheable then bit 2 .|. bit 3 else 0) .|.
>     (if xn then bit 4 else 0) .|.
>     (if global then 0 else bit 17) .|.
>     (fromIntegral $ fromEnum rights `shiftL` 10)

> data PTE
>     = InvalidPTE
>     | LargePagePTE {
>         pteFrame :: PAddr,
>         pteCacheable :: Bool,
>         pteGlobal :: Bool,
>         pteExecuteNever :: Bool,
>         pteRights :: VMRights }
>     | SmallPagePTE {
>         pteFrame :: PAddr,
>         pteCacheable :: Bool,
>         pteGlobal :: Bool,
>         pteExecuteNever :: Bool,
>         pteRights :: VMRights }
>     deriving (Show, Eq)

> wordFromPTE :: PTE -> Word
> wordFromPTE InvalidPTE = 0
> wordFromPTE (LargePagePTE frame cacheable global xn rights) = 1 .|.
>     (fromIntegral frame .&. 0xffff0000) .|.
>     (if cacheable then bit 2 .|. bit 3 else 0) .|.
>     (if global then 0 else bit 11) .|.
>     (if xn then bit 15 else 0) .|.
>     (fromIntegral $ fromEnum rights `shiftL` 4)
> wordFromPTE (SmallPagePTE frame cacheable global xn rights) = 2 .|.
>     (fromIntegral frame .&. 0xfffff000) .|.
>     (if xn then 1 else 0) .|.
>     (if cacheable then bit 2 .|. bit 3 else 0) .|.
>     (if global then 0 else bit 11) .|.
>     (fromIntegral $ fromEnum rights `shiftL` 4)

#else /* CONFIG_ARM_HYPERVISOR_SUPPORT */

Hypervisor extensions use long page table descriptors (64-bit) for the stage 2
translation (host-to-hypervisor). This is a three-level table system, but the
hardware can be configured to omit the first level entirely if all second
levels are stored contiguously. We use this configuration to preserve the usual
page table/directory nomenclature.

> -- FIXME ARMHYP global (SH) is never used so I don't know what a global page's SH would look like

seL4 does not use hardware domains or parity on ARM hypervisor systems.

> data PDE
>     = InvalidPDE
>     | PageTablePDE {
>         pdeTable :: PAddr }
>     | SectionPDE {
>         pdeFrame :: PAddr,
>         pdeCacheable :: Bool,
>         pdeExecuteNever :: Bool,
>         pdeRights :: VMRights }
>     | SuperSectionPDE {
>         pdeFrame :: PAddr,
>         pdeCacheable :: Bool,
>         pdeExecuteNever :: Bool,
>         pdeRights :: VMRights }
>     deriving (Show, Eq)

> hapFromVMRights :: VMRights -> Word
> hapFromVMRights VMKernelOnly = 0
> hapFromVMRights VMNoAccess = 0
> hapFromVMRights VMReadOnly = 1
> hapFromVMRights VMReadWrite = 3

> wordsFromPDE :: PDE -> [Word]
> wordsFromPDE InvalidPDE = [0, 0]
> wordsFromPDE (PageTablePDE table) = [w0, 0]
>     where w0 = 3 .|. (fromIntegral table .&. 0xfffff000)
> wordsFromPDE (SectionPDE frame cacheable xn rights) = [w0, w1]
>     where w1 = 0 .|. (if xn then bit 22 else 0) -- no contig. hint
>           w0 = 1 .|.
>                (fromIntegral frame .&. 0xfffff000) .|.
>                bit 10 .|. -- AF
>                (hapFromVMRights rights `shiftL` 6) .|.
>                (if cacheable then 0xf `shiftL` 2 else 0)
> wordsFromPDE (SuperSectionPDE frame cacheable xn rights) = [w0, w1]
>     where w1 = 0 .|. (if xn then bit 22 else 0) .|. bit 20 -- contig. hint
>           w0 = 1 .|.
>                (fromIntegral frame .&. 0xfffff000) .|.
>                bit 10 .|. -- AF
>                (hapFromVMRights rights `shiftL` 6) .|.
>                (if cacheable then 0xf `shiftL` 2 else 0)

> data PTE
>     = InvalidPTE
>     | LargePagePTE {
>         pteFrame :: PAddr,
>         pteCacheable :: Bool,
>         pteExecuteNever :: Bool,
>         pteRights :: VMRights }
>     | SmallPagePTE {
>         pteFrame :: PAddr,
>         pteCacheable :: Bool,
>         pteExecuteNever :: Bool,
>         pteRights :: VMRights }
>     deriving (Show, Eq)

> wordsFromPTE :: PTE -> [Word]
> wordsFromPTE InvalidPTE = [0, 0]
> wordsFromPTE (SmallPagePTE frame cacheable xn rights) = [w0, w1]
>     where w1 = 0 .|. (if xn then bit 22 else 0) .|. bit 20 -- contig. hint
>           w0 = 3 .|.
>                (fromIntegral frame .&. 0xfffff000) .|.
>                bit 10 .|. -- AF
>                (hapFromVMRights rights `shiftL` 6) .|.
>                (if cacheable then 0xf `shiftL` 2 else 0)
> wordsFromPTE (LargePagePTE frame cacheable xn rights) = [w0, w1]
>     where w1 = 0 .|. (if xn then bit 22 else 0) -- no contig. hint
>           w0 = 3 .|.
>                (fromIntegral frame .&. 0xfffff000) .|.
>                bit 10 .|. -- AF
>                (hapFromVMRights rights `shiftL` 6) .|.
>                (if cacheable then 0xf `shiftL` 2 else 0)

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

> data VMRights
>     = VMNoAccess
>     | VMKernelOnly
>     | VMReadOnly
>     | VMReadWrite
>     deriving (Show, Eq, Enum)

> data VMAttributes = VMAttributes {
>     armPageCacheable, armParityEnabled, armExecuteNever :: Bool }

Convenient references to size and log of size of PDEs and PTEs.

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

With hypervisor extensions enabled, page table and page directory entries occupy
8 bytes. Page directories occupy four frames, and page tables occupy a frame.

> pteBits = (3 :: Int)
> pdeBits = (3 :: Int)
> pdBits = (11 :: Int) + pdeBits
> ptBits = (9 :: Int) + pteBits
> vcpuBits = pageBits

#else /* CONFIG_ARM_HYPERVISOR_SUPPORT */

ARM page directories and page tables occupy four frames and one quarter of a frame, respectively.

> pteBits = (2 :: Int)
> pdeBits = (2 :: Int)
> pdBits = (12 :: Int) + pdeBits
> ptBits = (8 :: Int) + pteBits

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

> pteSize :: Int
> pteSize = bit pteBits
> pdeSize :: Int
> pdeSize = bit pdeBits

> cacheLineBits = Platform.cacheLineBits
> cacheLine = Platform.cacheLine

#ifdef CONFIG_ARM_SMMU

\subsubsection{IO Page Table Structure}

> ioptBits :: Int
> ioptBits = pageBits

FIXME ARMHYP this is really platform code (TK1), move there

Note that InvalidIOPDE and InvalidPTE do not exist in C, as there is no valid bit. What actually happens is that a non-read, non-write entry is considered invalid. In pracice, the kernel writes an IOPTE/IOPDE of all zeros here.

> data IOPDE
>     = InvalidIOPDE
>     | PageTableIOPDE {
>         iopdeFrame :: PAddr,
>         iopdeRead :: Bool,
>         iopdeWrite :: Bool,
>         iopdeNonsecure :: Bool }
>     | SectionIOPDE {
>         iopdeFrame :: PAddr,
>         iopdeRead :: Bool,
>         iopdeWrite :: Bool,
>         iopdeNonsecure :: Bool }
>     deriving (Show, Eq)

> iopteBits = 2 :: Int
> iopdeBits = 2 :: Int
> iopteSize = bit iopteBits :: Int
> iopdeSize = bit iopdeBits :: Int

> wordFromIOPDE :: IOPDE -> Word
> wordFromIOPDE InvalidIOPDE = 0
> wordFromIOPDE (PageTableIOPDE addr r w ns) = bit 28 .|.
>         ((fromIntegral addr .&. 0xfffffc00) `shiftR` 10) .|.
>         (if r then bit 31 else 0) .|.
>         (if w then bit 30 else 0) .|.
>         (if ns then bit 29 else 0)
> wordFromIOPDE (SectionIOPDE addr r w ns) = 0 .|.
>         ((fromIntegral addr .&. 0xffc00000) `shiftR` 12) .|.
>         (if r then bit 31 else 0) .|.
>         (if w then bit 30 else 0) .|.
>         (if ns then bit 29 else 0)

> data IOPTE
>     = InvalidIOPTE
>     | PageIOPTE {
>         iopteFrame :: PAddr,
>         iopteRead :: Bool,
>         iopteWrite :: Bool,
>         iopteNonsecure :: Bool }
>     deriving (Show, Eq)

> wordFromIOPTE :: IOPTE -> Word
> wordFromIOPTE InvalidIOPTE = 0
> wordFromIOPTE (PageIOPTE addr r w ns) = 0 .|.
>         ((fromIntegral addr .&. 0xfffff000) `shiftR` 12) .|.
>         (if r then bit 31 else 0) .|.
>         (if w then bit 30 else 0) .|.
>         (if ns then bit 29 else 0)

#endif /* CONFIG_ARM_SMMU */

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

\subsection{GIC VCPU interface}

> vgicIRQActive :: Word
> vgicIRQActive = 2 `shiftL` 28

> vgicIRQMask :: Word
> vgicIRQMask = 3 `shiftL` 28

> get_gic_vcpu_ctrl_hcr :: MachineMonad Word
> get_gic_vcpu_ctrl_hcr = error "FIXME ARMHYP Unimplemented callback"

> set_gic_vcpu_ctrl_hcr :: Word -> MachineMonad ()
> set_gic_vcpu_ctrl_hcr = error "FIXME ARMHYP Unimplemented callback"

> get_gic_vcpu_ctrl_vmcr :: MachineMonad Word
> get_gic_vcpu_ctrl_vmcr = error "FIXME ARMHYP Unimplemented callback"

> set_gic_vcpu_ctrl_vmcr :: Word -> MachineMonad ()
> set_gic_vcpu_ctrl_vmcr = error "FIXME ARMHYP Unimplemented callback"

> get_gic_vcpu_ctrl_apr :: MachineMonad Word
> get_gic_vcpu_ctrl_apr = error "FIXME ARMHYP Unimplemented callback"

> set_gic_vcpu_ctrl_apr :: Word -> MachineMonad ()
> set_gic_vcpu_ctrl_apr = error "FIXME ARMHYP Unimplemented callback"

> get_gic_vcpu_ctrl_vtr :: MachineMonad Word
> get_gic_vcpu_ctrl_vtr = error "FIXME ARMHYP Unimplemented callback"

> get_gic_vcpu_ctrl_eisr0 :: MachineMonad Word
> get_gic_vcpu_ctrl_eisr0 = error "FIXME ARMHYP Unimplemented callback"

> get_gic_vcpu_ctrl_eisr1 :: MachineMonad Word
> get_gic_vcpu_ctrl_eisr1 = error "FIXME ARMHYP Unimplemented callback"

> get_gic_vcpu_ctrl_misr :: MachineMonad Word
> get_gic_vcpu_ctrl_misr = error "FIXME ARMHYP Unimplemented callback"

> get_gic_vcpu_ctrl_lr :: Word -> MachineMonad Word
> get_gic_vcpu_ctrl_lr = error "FIXME ARMHYP Unimplemented callback"

> set_gic_vcpu_ctrl_lr :: Word -> Word -> MachineMonad ()
> set_gic_vcpu_ctrl_lr = error "FIXME ARMHYP Unimplemented callback"

\subsection{Virtual timer interface}

> get_cntv_cval_64 :: MachineMonad Word64
> get_cntv_cval_64 = error "FIXME ARMHYP Unimplemented callback"
> set_cntv_cval_64 :: Word64 -> MachineMonad ()
> set_cntv_cval_64 = error "FIXME ARMHYP Unimplemented callback"

> get_cntv_off_64 :: MachineMonad Word64
> get_cntv_off_64 = error "FIXME ARMHYP Unimplemented callback"
> set_cntv_off_64 :: Word64 -> MachineMonad ()
> set_cntv_off_64 = error "FIXME ARMHYP Unimplemented callback"

> read_cntpct :: MachineMonad Word64
> read_cntpct = error "FIXME ARMHYP Unimplemented callback"

> check_export_arch_timer :: MachineMonad ()
> check_export_arch_timer = error "FIXME ARMHYP Unimplemented callback"

#endif

\subsection{Constants}

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

> hcrCommon :: Word
> --          HCR_TSC | HCR_AMO  | HCR_IO | HCR_FMO | HCR_DC  | HCR_VM
> hcrCommon = bit 19 .|. bit 5  .|. bit 4 .|. bit 3 .|. bit 12 .|. bit 0

> hcrTWE :: Word
> hcrTWE = bit 14

> hcrTWI :: Word
> hcrTWI = bit 13

> hcrVCPU :: Word -- HCR_VCPU
> hcrVCPU = if config_DISABLE_WFI_WFE_TRAPS
>           then hcrCommon
>           else hcrCommon .|. hcrTWE .|. hcrTWI

> hcrNative = (0xFE8103B :: Word) -- HCR_NATIVE
> vgicHCREN = (0x1 :: Word) -- VGIC_HCR_EN
> sctlrDefault = (0xc5187c :: Word) -- SCTLR_DEFAULT
> actlrDefault = (0x40 :: Word) -- ACTLR_DEFAULT
> gicVCPUMaxNumLR = (64 :: Int)

> -- Wether to trap WFI/WFE instructions or not in hyp mode
> config_DISABLE_WFI_WFE_TRAPS :: Bool
> config_DISABLE_WFI_WFE_TRAPS = error "generated from CMake config"

#endif

\subsection{Config parameters}

> -- Whether to use the GICv3. Defaults to GICv2 when set to False.
> config_ARM_GIC_V3 :: Bool
> config_ARM_GIC_V3 = error "generated from CMake config"

> -- Whether the handleSpuriousIRQ machine op is available
> hasSpuriousIRQ_mop :: Bool
> hasSpuriousIRQ_mop = error "Implemented in MachineOps.thy"

> -- Whether the setTrigger machine op is available
> haveSetTrigger :: Bool
> haveSetTrigger = error "Implemented in machine/(ARM|ARM_HYP)/Platform.thy"

\subsection{SGI}

> numSGIs :: Int
> numSGIs = error "defined in machine/AARCH64/Platform.thy"

> gicNumTargets :: Int
> gicNumTargets = error "defined in machine/AARCH64/Platform.thy"

> isGICPlatform :: Bool
> isGICPlatform = error "defined in machine/AARCH64/Platform.thy"

> -- the machine op uses word_t (and irq_t which is also word_t in C)
> sendSGI :: Word -> Word -> MachineMonad ()
> sendSGI irq target = error "Unimplemented - machine op"
