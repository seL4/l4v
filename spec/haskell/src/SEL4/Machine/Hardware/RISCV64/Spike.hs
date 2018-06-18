-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

{-# LANGUAGE EmptyDataDecls, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}

module SEL4.Machine.Hardware.RISCV64.Spike where

import SEL4.Machine.RegisterSet
import Foreign.Ptr
import Data.Bits
import Data.Word(Word8, Word16)
import Data.Ix

data CallbackData

-- FIXME RISCV unchecked copypasta
newtype IRQ = IRQ Word8
    deriving (Enum, Ord, Ix, Eq, Show)

-- FIXME RISCV unchecked copypasta
instance Bounded IRQ where
    minBound = IRQ 0
    maxBound = IRQ 31

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
pageColourBits = error "FIXME RISCV TODO"

-- FIXME RISCV TODO

{- stubs -}

pptrBase :: VPtr
pptrBase = VPtr 0xFFFFFFC000000000

pptrUserTop :: VPtr
pptrUserTop = pptrBase

{- simulator callback stubs - we do not plan to support the simulator on this
   platform -}

getMemoryRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getMemoryRegions _ = error "FIXME RISCV TODO"

getDeviceRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getDeviceRegions _ = error "FIXME RISCV TODO"

getKernelDevices :: Ptr CallbackData -> IO [(PAddr, PPtr Word)]
getKernelDevices _ = error "FIXME RISCV TODO"

maskInterrupt :: Ptr CallbackData -> Bool -> IRQ -> IO ()
maskInterrupt env mask (IRQ irq) = error "FIXME RISCV TODO"

loadWordCallback :: Ptr CallbackData -> PAddr -> IO Word
loadWordCallback = error "FIXME RISCV TODO"

storeWordCallback :: Ptr CallbackData -> PAddr -> Word -> IO ()
storeWordCallback = error "FIXME RISCV TODO"

getActiveIRQ :: Ptr CallbackData -> IO (Maybe IRQ)
getActiveIRQ = error "FIXME RISCV TODO"

ackInterrupt :: Ptr CallbackData -> IRQ -> IO ()
ackInterrupt _ _ = error "FIXME RISCV TODO"

configureTimer :: Ptr CallbackData -> IO IRQ
configureTimer env = error "FIXME RISCV TODO"

resetTimer :: Ptr CallbackData -> IO ()
resetTimer env = error "FIXME RISCV TODO"
