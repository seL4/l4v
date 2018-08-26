-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

{-# LANGUAGE EmptyDataDecls, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}

module SEL4.Machine.Hardware.RISCV64.Spike where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet
import Foreign.Ptr
import Data.Bits
import Data.Word(Word8, Word16, Word32)
import Data.Ix

data CallbackData

newtype IRQ = IRQ Word32
    deriving (Enum, Ord, Ix, Eq, Show)

instance Bounded IRQ where
    minBound = IRQ 0
    maxBound = IRQ 5 -- no external interrupts supported yet on spike

newtype PAddr = PAddr { fromPAddr :: Word }
    deriving (Integral, Real, Show, Eq, Num, Bits, FiniteBits, Ord, Enum, Bounded)

kernelBase :: VPtr
kernelBase = VPtr 0xFFFFFFFF80000000

physBase = 0x0 -- called PADDR_BASE in C
physMappingOffset = fromVPtr pptrBase - physBase -- called BASE_OFFSET in C
paddrLoad = 0xC0000000
kernelBaseOffset = fromVPtr kernelBase - paddrLoad

ptrFromPAddr :: PAddr -> PPtr a
ptrFromPAddr (PAddr addr) = PPtr $ addr + physMappingOffset

addrFromPPtr :: PPtr a -> PAddr
addrFromPPtr (PPtr ptr) = PAddr $ ptr - physMappingOffset

addrFromKPPtr :: PPtr a -> PAddr
addrFromKPPtr (PPtr ptr) = PAddr $ ptr - kernelBaseOffset

pageColourBits :: Int
pageColourBits = error "unused on this architecture"

{- stubs -}

pptrBase :: VPtr
pptrBase = VPtr 0xFFFFFFC000000000

pptrUserTop :: VPtr
pptrUserTop = pptrBase

{- simulator callback stubs - we do not plan to support the simulator on this
   platform -}

getMemoryRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getMemoryRegions _ = error "unimplemented"

getDeviceRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getDeviceRegions _ = error "unimplemented"

getKernelDevices :: Ptr CallbackData -> IO [(PAddr, PPtr Word)]
getKernelDevices _ = error "unimplemented"

maskInterrupt :: Ptr CallbackData -> Bool -> IRQ -> IO ()
maskInterrupt env mask (IRQ irq) = error "unimplemented"

loadWordCallback :: Ptr CallbackData -> PAddr -> IO Word
loadWordCallback = error "unimplemented"

storeWordCallback :: Ptr CallbackData -> PAddr -> Word -> IO ()
storeWordCallback = error "unimplemented"

getActiveIRQ :: Ptr CallbackData -> IO (Maybe IRQ)
getActiveIRQ = error "unimplemented"

ackInterrupt :: Ptr CallbackData -> IRQ -> IO ()
ackInterrupt _ _ = error "unimplemented"

configureTimer :: Ptr CallbackData -> IO IRQ
configureTimer env = error "unimplemented"

resetTimer :: Ptr CallbackData -> IO ()
resetTimer env = error "unimplemented"
