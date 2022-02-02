--
-- Copyright 2022, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

{-# LANGUAGE EmptyDataDecls, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}

module SEL4.Machine.Hardware.AARCH64.TX2 where

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
    maxBound = IRQ 383

newtype PAddr = PAddr { fromPAddr :: Word }
    deriving (Integral, Real, Show, Eq, Num, Bits, FiniteBits, Ord, Enum, Bounded)

physBase :: PAddr
physBase = PAddr 0x80000000

pageColourBits :: Int
pageColourBits = error "unused on this architecture"

irqInvalid :: IRQ
irqInvalid = IRQ 0xFFFF -- -1 in 16 bits

irqVGICMaintenance = IRQ 25
irqVTimerEvent = IRQ 27
irqSMMU = IRQ 202

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
