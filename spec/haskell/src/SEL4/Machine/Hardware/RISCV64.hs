--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, EmptyDataDecls #-}

-- This module defines the low-level RISC-V hardware interface.

module SEL4.Machine.Hardware.RISCV64 where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet

import Foreign.Ptr
import Control.Monad.Reader
import Data.Bits
import Data.Word(Word8, Word16, Word32, Word64)

-- The RISC-V 64bit-specific register set definitions are qualified with the
-- "RISCV" prefix, and the platform-specific hardware access functions are
-- qualified with the "Platform" prefix.

import qualified SEL4.Machine.RegisterSet.RISCV64 as RISCV64
import qualified SEL4.Machine.Hardware.RISCV64.PLATFORM as Platform

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
    = RISCVSmallPage
    | RISCVLargePage
    | RISCVHugePage
    deriving (Show, Eq, Ord, Enum, Bounded)

-- C defines further fault types, but the trap handler only forwards these
-- below as VMFaults. The rest, including any unknown faults, become user level
-- faults with the fault scause number passed on verbatim.

data VMFaultType
    = RISCVInstructionAccessFault
    | RISCVLoadAccessFault
    | RISCVStoreAccessFault
    | RISCVInstructionPageFault
    | RISCVLoadPageFault
    | RISCVStorePageFault
    deriving Show

-- incomplete enumeration of VMFaultType, used only in handleVMFault, hence Word
vmFaultTypeFSR :: VMFaultType -> Word
vmFaultTypeFSR f =
    case f of
        RISCVInstructionAccessFault -> 1
        RISCVLoadAccessFault -> 5
        RISCVStoreAccessFault -> 7
        RISCVInstructionPageFault -> 12
        RISCVLoadPageFault -> 13
        RISCVStorePageFault -> 15

data HypFaultType
    = RISCVNoHypFaults
    deriving Show

{- Physical Memory -}

type PAddr = Platform.PAddr

fromPAddr :: PAddr -> Word
fromPAddr = Platform.fromPAddr

paddrBase :: PAddr
paddrBase = Platform.PAddr 0x0

pptrBase :: VPtr
pptrBase = VPtr 0xFFFFFFC000000000

pptrTop :: VPtr
pptrTop = VPtr 0xFFFFFFFF80000000

kernelELFPAddrBase :: PAddr
kernelELFPAddrBase = toPAddr $ (fromPAddr Platform.physBase) + 0x4000000

kernelELFBase :: VPtr
kernelELFBase = VPtr $ fromVPtr pptrTop + (fromPAddr kernelELFPAddrBase .&. (mask 30))

pptrUserTop :: VPtr
pptrUserTop = pptrBase

pptrBaseOffset = (fromVPtr pptrBase) - (fromPAddr paddrBase)

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
-- 2^3 bytes, thus occupying one small page.

ptTranslationBits :: Int
ptTranslationBits = 9

pteBits :: Int
pteBits = 3

ptBits :: Int
ptBits = ptTranslationBits + pteBits

pageBitsForSize :: VMPageSize -> Int
pageBitsForSize RISCVSmallPage = pageBits
pageBitsForSize RISCVLargePage = pageBits + ptTranslationBits
pageBitsForSize RISCVHugePage = pageBits + ptTranslationBits + ptTranslationBits

configureTimer :: MachineMonad IRQ
configureTimer = do
    cbptr <- ask
    liftIO $ Platform.configureTimer cbptr

setDeadline :: Word64 -> MachineMonad ()
setDeadline d = do
    cbptr <- ask
    liftIO $ Platform.setDeadline cbptr d

ackDeadlineIRQ :: MachineMonad ()
ackDeadlineIRQ = do
    cbptr <- ask
    liftIO $ Platform.ackDeadlineIRQ cbptr

resetTimer :: MachineMonad ()
resetTimer = do
    cbptr <- ask
    liftIO $ Platform.resetTimer cbptr

initIRQController :: MachineMonad ()
initIRQController = error "Unimplemented - boot code"

timerIRQ :: IRQ
timerIRQ = Platform.timerIRQ

setIRQTrigger :: IRQ -> Bool -> MachineMonad ()
setIRQTrigger irq trigger = error "Unimplemented - machine op"

getRestartPC = getRegister (Register RISCV64.FaultIP)
setNextPC = setRegister (Register RISCV64.NextIP)

{- Memory Management -}

-- There are several machine operations used by the memory management code to
-- access relevant hardware registers. They are relevant for simulator support
-- only in Haskell and are implemented separately in C and the proofs.

{- Cleaning Memory -}

-- This function is called before a region of user-memory is recycled.
-- It zeros every word to ensure that user tasks cannot access any private data
-- that might previously have been stored in the region.

clearMemory :: PPtr Word -> Int -> MachineMonad ()
clearMemory ptr byteLength = error "Unimplemented -- machine op"

-- This function is called before a region of memory is made user-accessible.
-- Though in Haskell, it is implemented as "clearMemory",
-- we draw the logical distinction to gain more freedom for its interpretation
-- in the Isabelle formalization.

initMemory :: PPtr Word -> Int -> MachineMonad ()
initMemory = clearMemory

-- This function is called to free a region of user-memory after use.
-- In Haskell, this operation does not do anything.
-- We just use it as a stub for the Isabelle formalization.

freeMemory :: PPtr Word -> Int -> MachineMonad ()
freeMemory _ _ = return ()

-- Same as "clearMemory", but uses storeWordVM to write to memory.
-- To be used when creating mapping objects (page tables and -dirs)
-- Flushing the kernel's mapping from TLBindexed
-- caches must be done separately.

clearMemoryVM :: PPtr Word -> Int -> MachineMonad ()
clearMemoryVM ptr bits = error "Unimplemented -- machine op"

{- Address Space Setup -}

setVSpaceRoot :: PAddr -> Word64 -> MachineMonad ()
setVSpaceRoot addr asid = error "Unimplemented - machine op"

{- Memory Barriers -}

sfence :: MachineMonad ()
sfence = error "Unimplemented - machine op"

{- Cache Cleaning and TLB Flushes -}

hwASIDFlush :: Word64 -> MachineMonad ()
hwASIDFlush asid = error "unimplemented - machine op"

{- Page Table Structure -}

data VMAttributes
    = VMAttributes { riscvExecuteNever :: Bool }

-- The C code also defines VMWriteOnly.
-- Leaving it out here will show that it is unused.
data VMRights
    = VMKernelOnly
    | VMReadOnly
    | VMReadWrite
    deriving (Show, Eq)

vmRightsToBits :: VMRights -> Word
vmRightsToBits VMKernelOnly = 1
vmRightsToBits VMReadOnly = 2
vmRightsToBits VMReadWrite = 3

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
--  - dirty and accessed bits are always 1 for valid PTEs
--   - SW bits always 0
--   - valid = 1 and read/write/execute = 0 => table PTE
--   - valid = 0 => invalid PTE
--   - otherwise => page PTE

data PTE
    = InvalidPTE
    | PagePTE {
        ptePPN :: PAddr,
        pteGlobal :: Bool,
        pteUser :: Bool,
        pteExecute :: Bool,
        pteRights :: VMRights }
    | PageTablePTE {
        ptePPN :: PAddr,
        pteGlobal :: Bool }
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

getCurrentTime :: MachineMonad Word64
getCurrentTime = do
    cbptr <- ask
    liftIO $ Platform.getCurrentTime cbptr

timerPrecision :: Word64
timerPrecision = usToTicks 1

usToTicks :: Word64 -> Word64
usToTicks _ = undefined

ticksToUs :: Word64 -> Word64
ticksToUs _ = undefined

maxUsToTicks :: Word64
maxUsToTicks = undefined

maxTicksToUs :: Word64
maxTicksToUs = undefined

maxPeriodUs :: Word64
maxPeriodUs = undefined

debugPrint :: String -> MachineMonad ()
debugPrint str = liftIO $ putStrLn str

read_stval :: MachineMonad Word
read_stval = error "Unimplemented - machine op"

plic_complete_claim :: IRQ -> MachineMonad ()
plic_complete_claim = error "Unimplemented - machine op"
