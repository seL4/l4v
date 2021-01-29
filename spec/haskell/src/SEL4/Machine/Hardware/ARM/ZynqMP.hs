--
-- Copyright 2014, General Dynamics C4 Systems
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This file is kept mostly for Haskell compatibility with other platforms.
-- Almost all values defined below are being overridden in Isabelle later.

{-# LANGUAGE EmptyDataDecls, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}

module SEL4.Machine.Hardware.ARM.ZynqMP where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet
import Foreign.Ptr
import Data.Bits
import Data.Word(Word8)
import Data.Ix
import SEL4.Machine.Hardware.ARM.Callbacks

newtype IRQ = IRQ Word8
    deriving (Enum, Ord, Ix, Eq, Show)

instance Bounded IRQ where
    minBound = IRQ 0
    maxBound = IRQ 187


kernelBase :: VPtr
kernelBase = VPtr 0xe0000000

physBase = 0x0
physMappingOffset = 0xe0000000 - physBase

ptrFromPAddr :: PAddr -> PPtr a
ptrFromPAddr (PAddr addr) = PPtr $ addr + physMappingOffset

addrFromPPtr :: PPtr a -> PAddr
addrFromPPtr (PPtr ptr) = PAddr $ ptr - physMappingOffset

pageColourBits :: Int
pageColourBits = 0

getMemoryRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getMemoryRegions _ = return [(0x80000000, 0x80000000 + (0x8 `shiftL` 24))]

getDeviceRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getDeviceRegions _ = return devices
    where devices = [
            (0x53f98000, 0x53f99000) -- second SP804; kernel uses first
            ]

timerPPtr = PPtr 0xfff00000
timerAddr = PAddr 0x53f94000
timerIRQ = IRQ 28

avicPPtr = PPtr 0xfff01000
avicAddr = PAddr 0x68000000

getKernelDevices :: Ptr CallbackData -> IO [(PAddr, PPtr Word)]
getKernelDevices _ = return devices
    where devices = [
            (timerAddr, timerPPtr), -- kernel timer
            (avicAddr, avicPPtr) -- interrupt controller
            ]

maskInterrupt :: Ptr CallbackData -> Bool -> IRQ -> IO ()
maskInterrupt env mask (IRQ irq) = do
    let value = fromIntegral irq
    offset <- return $ if (mask == True) then 0xc else 0x8
    storeWordCallback env (avicAddr + offset) value

ackInterrupt :: Ptr CallbackData -> IRQ -> IO ()
ackInterrupt _ _ = return () -- overridden in Isabelle

getActiveIRQ :: Ptr CallbackData -> IO (Maybe IRQ)
getActiveIRQ _ = return Nothing -- overridden in Isabelle

-- 1kHz tick; qemu's SP804s always run at 1MHz
timerFreq :: Word
timerFreq = 100

timerLimit :: Word
timerLimit = 1000000 `div` timerFreq

configureTimer :: Ptr CallbackData -> IO IRQ
configureTimer env = do
    -- enabled, periodic, interrupts enabled
    storeWordCallback env timerAddr 0
    let timerCtrl = bit 24 .|. bit 17 .|. bit 3 .|. bit 2 .|. bit 1
    storeWordCallback env timerAddr timerCtrl
    storeWordCallback env (timerAddr+0x8) (100 * 1000 * 1000)
    storeWordCallback env (timerAddr+0xc) 0
    storeWordCallback env (timerAddr+0x4) 1
    let timerCtrl2 = timerCtrl .|. 1
    storeWordCallback env timerAddr timerCtrl2
    return timerIRQ

initIRQController :: Ptr CallbackData -> IO ()
initIRQController _ = return ()

resetTimer :: Ptr CallbackData -> IO ()
resetTimer _ = return ()

isbCallback :: Ptr CallbackData -> IO ()
isbCallback _ = return ()

dsbCallback :: Ptr CallbackData -> IO ()
dsbCallback _ = return ()

dmbCallback :: Ptr CallbackData -> IO ()
dmbCallback _ = return ()

cacheCleanByVACallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanByVACallback _cptr _mva _pa = return ()

cacheCleanByVA_PoUCallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanByVA_PoUCallback _cptr _mva _pa = return ()

cacheInvalidateByVACallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheInvalidateByVACallback _cptr _mva _pa = return ()

cacheInvalidateByVA_ICallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheInvalidateByVA_ICallback _cptr _mva _pa = return ()

cacheInvalidate_I_PoUCallback :: Ptr CallbackData -> IO ()
cacheInvalidate_I_PoUCallback _ = return ()

cacheCleanInvalidateByVACallback ::
    Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanInvalidateByVACallback _cptr _mva _pa = return ()

branchFlushCallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
branchFlushCallback _cptr _mva _pa = return ()

cacheClean_D_PoUCallback :: Ptr CallbackData -> IO ()
cacheClean_D_PoUCallback _ = return ()

cacheCleanInvalidate_D_PoCCallback :: Ptr CallbackData -> IO ()
cacheCleanInvalidate_D_PoCCallback _ = return ()

cacheCleanInvalidate_D_PoUCallback :: Ptr CallbackData -> IO ()
cacheCleanInvalidate_D_PoUCallback _ = return ()

cacheCleanInvalidateL2RangeCallback ::
    Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheCleanInvalidateL2RangeCallback _ _ _ = return ()

cacheInvalidateL2RangeCallback :: Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheInvalidateL2RangeCallback _ _ _ = return ()

cacheCleanL2RangeCallback :: Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheCleanL2RangeCallback _ _ _ = return ()

cacheLine :: Int
cacheLine = 32

cacheLineBits :: Int
cacheLineBits = 5
