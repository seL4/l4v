--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, EmptyDataDecls #-}

-- This module defines the low-level AARCH64 hardware interface.

module SEL4.Machine.Hardware.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet

import Foreign.Ptr
import Control.Monad.Reader
import Data.Bits
import Data.Word(Word8, Word16, Word32, Word64)

-- The AARCH64-specific register set definitions are qualified with the
-- "AARCH64" prefix, and the platform-specific hardware access functions are
-- qualified with the "Platform" prefix.

import qualified SEL4.Machine.RegisterSet.AARCH64 as AARCH64
import qualified SEL4.Machine.Hardware.AARCH64.PLATFORM as Platform

{- Data Types -}

-- The machine monad contains a platform-specific opaque pointer, used by the
-- external simulator interface.

type MachineMonad = ReaderT MachineData IO

type MachineData = Ptr Platform.CallbackData

type IRQ = Platform.IRQ

toPAddr = Platform.PAddr

{- Virtual Memory -}

-- these correspond to 4K, Mega and Giga pages in C

data VMPageSize
    = ARMSmallPage
    | ARMLargePage
    | ARMHugePage
    deriving (Show, Eq, Ord, Enum, Bounded)

data PT_Type = VSRootPT_T | NormalPT_T
    deriving (Show, Eq)

data VMFaultType
    = ARMDataAbort
    | ARMPrefetchAbort
    deriving Show

data HypFaultType
    = ARMVCPUFault Word32 -- HSR
    deriving Show

{- Physical Memory -}

type PAddr = Platform.PAddr

fromPAddr :: PAddr -> Word
fromPAddr = Platform.fromPAddr

paddrBase :: PAddr
paddrBase = Platform.PAddr 0x0

pptrBase :: VPtr
pptrBase = VPtr 0x0000008000000000

pptrTop :: VPtr
pptrTop = VPtr 0x000000FFC0000000

kernelELFPAddrBase :: PAddr
kernelELFPAddrBase = toPAddr $ (fromPAddr Platform.physBase) + 0x4000000

kernelELFBase :: VPtr
kernelELFBase = VPtr $ fromVPtr pptrTop + (fromPAddr kernelELFPAddrBase .&. (mask 30))

pptrUserTop :: VPtr
pptrUserTop = pptrBase

pptrBaseOffset :: Word
pptrBaseOffset = (fromVPtr pptrBase) - (fromPAddr paddrBase)

paddrTop :: PAddr
paddrTop = toPAddr $ (fromVPtr pptrTop - pptrBaseOffset)

ptrFromPAddr :: PAddr -> PPtr a
ptrFromPAddr addr = PPtr $ fromPAddr addr + pptrBaseOffset

addrFromPPtr :: PPtr a -> PAddr
addrFromPPtr addr = toPAddr $ fromPPtr addr - pptrBaseOffset

kernelELFBaseOffset = (fromVPtr kernelELFBase) - (fromPAddr kernelELFPAddrBase)

addrFromKPPtr :: PPtr a -> PAddr
addrFromKPPtr (PPtr addr) = toPAddr $ addr - kernelELFBaseOffset

{- Hardware Access -}

pageBits :: Int
pageBits = 12

-- Each page table performs 9 bits of translation, with each entry occupying
-- 2^3 bytes, thus occupying one small page, apart from top-level tables which
-- contain twice as many entries if config_ARM_PA_SIZE_BITS_40 is set.

ptTranslationBits :: PT_Type -> Int
ptTranslationBits pt_t =
    if pt_t == VSRootPT_T && config_ARM_PA_SIZE_BITS_40 then 10 else 9

pteBits :: Int
pteBits = 3

ptBits :: PT_Type -> Int
ptBits pt_t = ptTranslationBits pt_t + pteBits

-- The top-level table cannot contain frame PTEs, so only NormalPT_T
pageBitsForSize :: VMPageSize -> Int
pageBitsForSize ARMSmallPage = pageBits
pageBitsForSize ARMLargePage = pageBits + ptTranslationBits NormalPT_T
pageBitsForSize ARMHugePage = pageBits + ptTranslationBits NormalPT_T + ptTranslationBits NormalPT_T

vcpuBits :: Int
vcpuBits = 12

configureTimer :: MachineMonad IRQ
configureTimer = do
    cbptr <- ask
    liftIO $ Platform.configureTimer cbptr

resetTimer :: MachineMonad ()
resetTimer = do
    cbptr <- ask
    liftIO $ Platform.resetTimer cbptr

initIRQController :: MachineMonad ()
initIRQController = error "Unimplemented - boot code"

setIRQTrigger :: IRQ -> Bool -> MachineMonad ()
setIRQTrigger irq trigger = error "Unimplemented - machine op"

getRestartPC = getRegister (Register AARCH64.FaultIP)
setNextPC = setRegister (Register AARCH64.NextIP)

{- Memory Management -}

-- There are several machine operations used by the memory management code to
-- access relevant hardware registers. They are relevant for simulator support
-- only in Haskell and are implemented separately in C and the proofs.

{- Cleaning Memory -}

-- This function is called before a region of user-memory is recycled.
-- It zeros every word to ensure that user tasks cannot access any private data
-- that might previously have been stored in the region.

-- This function's abstract definition is in MachineOps.thy

clearMemory :: PPtr Word -> Int -> MachineMonad ()
clearMemory ptr byteLength = error "Unimplemented -- machine op"

-- This function is called before a region of memory is made user-accessible.
-- Though in Haskell, it is implemented as "clearMemory",
-- we draw the logical distinction to gain more freedom for its interpretation
-- in the Isabelle formalisation.

initMemory :: PPtr Word -> Int -> MachineMonad ()
initMemory = clearMemory

-- This function is called to free a region of user-memory after use.
-- In Haskell, this operation does not do anything.
-- We just use it as a stub for the Isabelle formalisation.

freeMemory :: PPtr Word -> Int -> MachineMonad ()
freeMemory _ _ = return ()

-- Same as "clearMemory", but uses storeWordVM to write to memory.
-- To be used when creating mapping objects (page tables)
-- Flushing the kernel's mapping from TLB-indexed
-- caches must be done separately.

clearMemoryVM :: PPtr Word -> Int -> MachineMonad ()
clearMemoryVM ptr bits = error "Unimplemented -- machine op"

{- Address Space Setup -}

setVSpaceRoot :: PAddr -> Word64 -> MachineMonad ()
setVSpaceRoot addr asid = error "Unimplemented - machine op"

{- Memory Barriers -}

isb :: MachineMonad ()
isb = error "Unimplemented - machine op"

dsb :: MachineMonad ()
dsb = error "Unimplemented - machine op"

dmb :: MachineMonad ()
dmb = error "Unimplemented - machine op"

{- Cache Cleaning and TLB Flushes -}

invalidateTranslationASID :: Word -> MachineMonad ()
invalidateTranslationASID vmID = error "unimplemented - machine op"

invalidateTranslationSingle :: Word -> MachineMonad ()
invalidateTranslationSingle vpn = error "unimplemented - machine op"

cleanByVA_PoU :: VPtr -> PAddr -> MachineMonad ()
cleanByVA_PoU vaddr paddr = error "Unimplemented - machine op"

cleanInvalidateCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
cleanInvalidateCacheRange_RAM vstart vend pstart = error "Unimplemented - machine op"

cleanCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
cleanCacheRange_RAM vstart vend pstart = error "Unimplemented - machine op"

cleanCacheRange_PoU :: VPtr -> VPtr -> PAddr -> MachineMonad ()
cleanCacheRange_PoU vstart vend pstart = error "Unimplemented - machine op"

invalidateCacheRange_RAM :: VPtr -> VPtr -> PAddr -> MachineMonad ()
invalidateCacheRange_RAM vstart vend pstart = error "Unimplemented - machine op"

invalidateCacheRange_I :: VPtr -> VPtr -> PAddr -> MachineMonad ()
invalidateCacheRange_I vstart vend pstart = error "Unimplemented - machine op"

branchFlushRange :: VPtr -> VPtr -> PAddr -> MachineMonad ()
branchFlushRange vstart vend pstart = error "Unimplemented - machine op"


{- FPU status/control registers -}

enableFpuEL01 :: MachineMonad ()
enableFpuEL01 = error "Unimplemented - machine op"

{- Fault registers -}

getFAR :: MachineMonad VPtr
getFAR = error "Unimplemented - machine op"

{- Hypervisor-specific status/control registers -}

setHCR :: Word -> MachineMonad ()
setHCR _hcr = error "Unimplemented - machine op"

getESR :: MachineMonad Word
getESR = error "Unimplemented - machine op"

addressTranslateS1 :: VPtr -> MachineMonad VPtr
addressTranslateS1 = error "Unimplemented - machine op"

getSCTLR :: MachineMonad Word
getSCTLR = error "Unimplemented - machine op"

setSCTLR :: Word -> MachineMonad ()
setSCTLR _sctlr = error "Unimplemented - machine op"

{- Hypervisor banked registers -}

-- Rather than a line-for-line copy of every hypervisor register storage and
-- retrieval function from the C code, we abstract the concept into one function
-- each. Some special registers, like SCTLR, still get their own load/store
-- functions due to being operated on separately.

readVCPUHardwareReg :: AARCH64.VCPUReg -> MachineMonad Word
readVCPUHardwareReg reg = error "Unimplemented - machine op"

writeVCPUHardwareReg :: AARCH64.VCPUReg -> Word -> MachineMonad ()
writeVCPUHardwareReg reg val = error "Unimplemented - machine op"

{- Page Table Structure -}

data VMAttributes
    = VMAttributes {
        armExecuteNever :: Bool,
        -- armParityEnabled not used in AARCH64
        armPageCacheable :: Bool }

-- The C code also defines VMWriteOnly.
-- Leaving it out here will show that it is unused.
data VMRights
    = VMKernelOnly
    | VMReadOnly
    | VMReadWrite
    deriving (Show, Eq)

vmRightsToBits :: VMRights -> Word
vmRightsToBits VMKernelOnly = 0
vmRightsToBits VMReadOnly = 3
vmRightsToBits VMReadWrite = 1

allowWrite :: VMRights -> Bool
allowWrite VMKernelOnly = False
allowWrite VMReadOnly = False
allowWrite VMReadWrite = True

allowRead :: VMRights -> Bool
allowRead VMKernelOnly = False
allowRead VMReadOnly = True
allowRead VMReadWrite = True

getVMRights :: Bool -> Bool -> VMRights
getVMRights True True = VMReadWrite
getVMRights False True = VMReadOnly
getVMRights _ _ = VMKernelOnly

vmRightsFromBits ::  Word -> VMRights
vmRightsFromBits rw = getVMRights (testBit rw 1) (testBit rw 0)

-- Page Table entries

--  Encoding notes:
--  - pteSmallPage distinguishes pte_4k_page from pte_page
--  - AF is always 1
--  - mair/mair_s2 (Memory Attribute Indirection Register) encoded as pteDevice

data PTE
    = InvalidPTE
    | PagePTE {
        pteBaseAddress :: PAddr,
        pteSmallPage :: Bool,
        pteGlobal :: Bool,
        pteExecuteNever :: Bool,
        pteDevice :: Bool,
        pteRights :: VMRights }
    | PageTablePTE {
        ptePPN :: PAddr }
    deriving (Show, Eq)

{- Simulator callbacks -}

pageColourBits :: Int
pageColourBits = Platform.pageColourBits

getMemoryRegions :: MachineMonad [(PAddr, PAddr)]
getMemoryRegions = do
    cpbtr <- ask
    liftIO $ Platform.getMemoryRegions cpbtr

getDeviceRegions :: MachineMonad [(PAddr, PAddr)]
getDeviceRegions = do
    cbptr <- ask
    liftIO $ Platform.getDeviceRegions cbptr

getKernelDevices :: MachineMonad [(PAddr, PPtr Word)]
getKernelDevices = do
    cbptr <- ask
    liftIO $ Platform.getKernelDevices cbptr

storeWord :: PPtr Word -> Word -> MachineMonad ()
storeWord ptr val = do
    cbptr <- ask
    liftIO $ Platform.storeWordCallback cbptr (addrFromPPtr ptr) val

storeWordVM :: PPtr Word -> Word -> MachineMonad ()
storeWordVM ptr val = storeWord ptr val

loadWord :: PPtr Word -> MachineMonad Word
loadWord ptr = do
    cbptr <- ask
    liftIO $ Platform.loadWordCallback cbptr $ addrFromPPtr ptr

getActiveIRQ :: Bool -> MachineMonad (Maybe IRQ)
getActiveIRQ _ = do
    cbptr <- ask
    liftIO $ Platform.getActiveIRQ cbptr

ackInterrupt :: IRQ -> MachineMonad ()
ackInterrupt irq = do
    cbptr <- ask
    liftIO $ Platform.ackInterrupt cbptr irq

maskInterrupt :: Bool -> IRQ -> MachineMonad ()
maskInterrupt maskI irq = do
    cbptr <- ask
    liftIO $ Platform.maskInterrupt cbptr maskI irq

deactivateInterrupt :: IRQ -> MachineMonad ()
deactivateInterrupt irq = error "Unimplemented - GICv3 machine op"

debugPrint :: String -> MachineMonad ()
debugPrint str = liftIO $ putStrLn str

{- FPU Operations -}

fpuThreadDeleteOp :: Word -> MachineMonad ()
fpuThreadDeleteOp tcbPtr = error "Unimplemented callback"

isFpuEnable :: MachineMonad Bool
isFpuEnable = error "Unimplemented - lazy FPU switch abstracted as machine op"

{- GIC VCPU interface -}

get_gic_vcpu_ctrl_hcr :: MachineMonad Word32
get_gic_vcpu_ctrl_hcr = error "Unimplemented - machine op"

set_gic_vcpu_ctrl_hcr :: Word32 -> MachineMonad ()
set_gic_vcpu_ctrl_hcr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_vmcr :: MachineMonad Word32
get_gic_vcpu_ctrl_vmcr = error "Unimplemented - machine op"

set_gic_vcpu_ctrl_vmcr :: Word32 -> MachineMonad ()
set_gic_vcpu_ctrl_vmcr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_apr :: MachineMonad Word32
get_gic_vcpu_ctrl_apr = error "Unimplemented - machine op"

set_gic_vcpu_ctrl_apr :: Word32 -> MachineMonad ()
set_gic_vcpu_ctrl_apr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_vtr :: MachineMonad Word32
get_gic_vcpu_ctrl_vtr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_eisr0 :: MachineMonad Word32
get_gic_vcpu_ctrl_eisr0 = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_eisr1 :: MachineMonad Word32
get_gic_vcpu_ctrl_eisr1 = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_misr :: MachineMonad Word32
get_gic_vcpu_ctrl_misr = error "Unimplemented - machine op"

get_gic_vcpu_ctrl_lr :: Word -> MachineMonad Word
get_gic_vcpu_ctrl_lr = error "Unimplemented - machine op"

set_gic_vcpu_ctrl_lr :: Word -> Word -> MachineMonad ()
set_gic_vcpu_ctrl_lr = error "Unimplemented - machine op"

{- Virtual timer interface -}

read_cntpct :: MachineMonad Word64
read_cntpct = error "Unimplemented - machine op"

check_export_arch_timer :: MachineMonad ()
check_export_arch_timer = error "Unimplemented - machine op"


{- Constants -}

hcrCommon :: Word
--          HCR_VM  | HCR_RW   | HCR_AMO | HCR_IMO | HCR_FMO | HCR_TSC
hcrCommon = bit 0  .|. bit 31 .|. bit 5 .|. bit 4 .|. bit 3 .|. bit 19

hcrTWE :: Word
hcrTWE = bit 14

hcrTWI :: Word
hcrTWI = bit 13

hcrVCPU :: Word -- HCR_VCPU
hcrVCPU = if config_DISABLE_WFI_WFE_TRAPS
          then hcrCommon
          else hcrCommon .|. hcrTWE .|. hcrTWI

hcrNative = (0x8E28103B :: Word) -- HCR_NATIVE
sctlrEL1VM = (0x34d58820 :: Word) -- SCTLR_EL1_VM
sctlrDefault  = (0x34d59824 :: Word) -- SCTLR_DEFAULT
vgicHCREN = (0x1 :: Word32) -- VGIC_HCR_EN
gicVCPUMaxNumLR = (64 :: Int)


{- Software-Generated Interrupts (SGI) -}

numSGIs :: Int
numSGIs = error "defined in machine/AARCH64/Platform.thy"

-- SGI targets
gicNumTargets :: Int
gicNumTargets = error "defined in machine/AARCH64/Platform.thy"

-- the machine op uses word_t (and irq_t which is also word_t in C)
sendSGI :: Word -> Word -> MachineMonad ()
sendSGI irq target = error "Unimplemented - machine op"


{- Config parameters -}

-- The size of the physical address space in hyp mode can be configured on some platforms.
config_ARM_PA_SIZE_BITS_40 :: Bool
config_ARM_PA_SIZE_BITS_40 = error "generated from CMake config"

-- Whether to trap WFI/WFE instructions or not in hyp mode.
config_DISABLE_WFI_WFE_TRAPS :: Bool
config_DISABLE_WFI_WFE_TRAPS = error "generated from CMake config"

-- Whether to use the GICv3. Defaults to GICv2 when set to False.
config_ARM_GIC_V3 :: Bool
config_ARM_GIC_V3 = error "generated from CMake config"
