-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, EmptyDataDecls #-}

-- This module defines the low-level RISC-V hardware interface.

module SEL4.Machine.Hardware.RISCV64 where

import SEL4.Machine.RegisterSet

import Foreign.Ptr
import Control.Monad.Reader
import Data.Bits
import Data.Word(Word8, Word16, Word32, Word64)

-- The RISC-V 64bit-specific register set definitions are qualified with the
-- "RISCV" prefix, and the platform-specific hardware access functions are
-- qualified with the "Platform" prefix.

import qualified SEL4.Machine.RegisterSet.RISCV64 as RISCV
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

data VMFaultType -- FIXME RISCV TODO
    = FIXMERISCVFaultType
    deriving Show

data HypFaultType -- FIXME RISCV TODO
    = RISCVNoHypFaults
    deriving Show

{- Physical Memory -}

type PAddr = Platform.PAddr

ptrFromPAddr :: PAddr -> PPtr a
ptrFromPAddr = Platform.ptrFromPAddr

addrFromPPtr :: PPtr a -> PAddr
addrFromPPtr = Platform.addrFromPPtr

fromPAddr :: PAddr -> Word
fromPAddr = Platform.fromPAddr

-- FIXME RISCV: do we need addrFromKPPtr like x64?

{- Hardware Access -}

pageBitsForSize :: VMPageSize -> Int
pageBitsForSize RISCVSmallPage = error "FIXME RISCV TODO"
pageBitsForSize RISCVLargePage = error "FIXME RISCV TODO"
pageBitsForSize RISCVHugePage = error "FIXME RISCV TODO"

pageBits :: Int
pageBits = error "FIXME RISCV TODO"

ptBits :: Int
ptBits = error "FIXME RISCV TODO"

-- FIXME RISCV TODO

setInterruptMode :: IRQ -> Bool -> Bool -> MachineMonad ()
setInterruptMode _ _ _ = error "FIXME RISCV TODO"

configureTimer :: MachineMonad IRQ
configureTimer = do
    cbptr <- ask
    liftIO $ Platform.configureTimer cbptr

resetTimer :: MachineMonad ()
resetTimer = do
    cbptr <- ask
    liftIO $ Platform.resetTimer cbptr

getRestartPC = error "FIXME RISCV TODO" -- getRegister (Register FIXME.FaultIP)
setNextPC = error "FIXME RISCV TODO" -- setRegister (Register FIXME.NextIP)

{- Memory Management -}

-- There are several operations used by the memory management code to access
-- relevant hardware registers.

{- Cleaning Memory -}

-- This function is called before a region of user-memory is recycled.
-- It zeros every word to ensure that user tasks cannot access any private data
-- that might previously have been stored in the region.

-- FIXME RISCV TODO

clearMemory :: PPtr Word -> Int -> MachineMonad ()
clearMemory ptr byteLength = error "FIXME RISCV TODO"

-- This function is called before a region of memory is made user-accessible.
-- Though in Haskell, it is implemented as "clearMemory",
-- we draw the logical distinction to gain more freedom for its interpretation
-- in the Isabelle formalization.

initMemory :: PPtr Word -> Int -> MachineMonad ()
initMemory = error "FIXME RISCV TODO"

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
clearMemoryVM ptr bits = error "FIXME RISCV TODO"

{- Address Space Setup -}

-- FIXME RISCV TODO

{- Memory Barriers -}

-- FIXME RISCV TODO

{- Cache Cleaning and TLB Flushes -}

-- FIXME RISCV TODO

{- Page Table Structure -}

data VMAttributes
    = VMAttributes { riscvExecuteNever :: Bool }

{- The C code also defines VMWriteOnly.
   Leaving it out here will show that it is unused. -}
data VMRights
    = VMKernelOnly
    | VMReadOnly
    | VMReadWrite
    deriving (Show, Eq)

vmRightsToBits :: VMRights -> Word
vmRightsToBits VMKernelOnly = 0x00
vmRightsToBits VMReadOnly = 0x01
vmRightsToBits VMReadWrite = 0x11

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

data PTE
    = InvalidPTE
    | SmallPagePTE {
        ptePPN :: PAddr,
        pteSW :: (Bool, Bool),
        pteDirty :: Bool,
        pteAccessed :: Bool,
        pteGlobal :: Bool,
        pteUser :: Bool,
        pteExecute :: Bool,
        pteRights :: VMRights,
        pteValid :: Bool }
    deriving (Show, Eq)

pptrBase :: VPtr
pptrBase = Platform.pptrBase

physBase :: PAddr
physBase = toPAddr Platform.physBase

-- IRQ parameters

-- FIXME RISCV TODO

{- Simulator callbacks -}

pageColourBits :: Int
pageColourBits = error "FIXME RISCV TODO" -- Platform.pageColourBits

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

debugPrint :: String -> MachineMonad ()
debugPrint str = liftIO $ putStrLn str

initIRQController :: MachineMonad ()
initIRQController = error "Unimplemented"
