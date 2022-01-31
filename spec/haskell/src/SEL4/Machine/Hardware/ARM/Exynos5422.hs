--
-- Copyright 2014, General Dynamics C4 Systems
--
-- SPDX-License-Identifier: GPL-2.0-only
--

{-# LANGUAGE EmptyDataDecls, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}

-- this is mostly a copy of KZM with extra info for virtualisation thrown in
-- FIXME ARMHYP TODO review other constants against C!
module SEL4.Machine.Hardware.ARM.Exynos5422 where

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
    maxBound = IRQ 254

physBase :: PAddr
physBase = PAddr 0x60000000

pptrBase :: VPtr
pptrBase = VPtr 0xe0000000

irqVGICMaintenance = IRQ 25
irqVTimerEvent = IRQ 27
irqSMMU = IRQ 109

cacheLine :: Int
cacheLine = 64

cacheLineBits :: Int
cacheLineBits = 6

{- simulator callback stubs - we do not plan to support the simulator on this
   platform -}

pageColourBits :: Int
pageColourBits = error "unimplemented"

getMemoryRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getMemoryRegions _ = error "unimplemented"

getDeviceRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getDeviceRegions _ = error "unimplemented"

getKernelDevices :: Ptr CallbackData -> IO [(PAddr, PPtr Word)]
getKernelDevices _ = error "unimplemented"

maskInterrupt :: Ptr CallbackData -> Bool -> IRQ -> IO ()
maskInterrupt _ _ _ = error "unimplemented"

ackInterrupt :: Ptr CallbackData -> IRQ -> IO ()
ackInterrupt _ _ = error "unimplemented"

getActiveIRQ :: Ptr CallbackData -> IO (Maybe IRQ)
getActiveIRQ _ = error "unimplemented"

configureTimer :: Ptr CallbackData -> IO IRQ
configureTimer _ = error "unimplemented"

initIRQController :: Ptr CallbackData -> IO ()
initIRQController _ = error "unimplemented"

resetTimer :: Ptr CallbackData -> IO ()
resetTimer _ = error "unimplemented"

isbCallback :: Ptr CallbackData -> IO ()
isbCallback _ = error "unimplemented"

dsbCallback :: Ptr CallbackData -> IO ()
dsbCallback _ = error "unimplemented"

dmbCallback :: Ptr CallbackData -> IO ()
dmbCallback _ = error "unimplemented"

cacheCleanByVACallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanByVACallback _ _ _ = error "unimplemented"

cacheCleanByVA_PoUCallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanByVA_PoUCallback _ _ _ = error "unimplemented"

cacheInvalidateByVACallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheInvalidateByVACallback _ _ _ = error "unimplemented"

cacheInvalidateByVA_ICallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheInvalidateByVA_ICallback _ _ _ = error "unimplemented"

cacheInvalidate_I_PoUCallback :: Ptr CallbackData -> IO ()
cacheInvalidate_I_PoUCallback _ = error "unimplemented"

cacheCleanInvalidateByVACallback ::
    Ptr CallbackData -> VPtr -> PAddr -> IO ()
cacheCleanInvalidateByVACallback _ _ _ = error "unimplemented"

branchFlushCallback :: Ptr CallbackData -> VPtr -> PAddr -> IO ()
branchFlushCallback _ _ _ = error "unimplemented"

cacheClean_D_PoUCallback :: Ptr CallbackData -> IO ()
cacheClean_D_PoUCallback _ = error "unimplemented"

cacheCleanInvalidate_D_PoCCallback :: Ptr CallbackData -> IO ()
cacheCleanInvalidate_D_PoCCallback _ = error "unimplemented"

cacheCleanInvalidate_D_PoUCallback :: Ptr CallbackData -> IO ()
cacheCleanInvalidate_D_PoUCallback _ = error "unimplemented"

cacheCleanInvalidateL2RangeCallback ::
    Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheCleanInvalidateL2RangeCallback _ _ _ = error "unimplemented"

cacheInvalidateL2RangeCallback :: Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheInvalidateL2RangeCallback _ _ _ = error "unimplemented"

cacheCleanL2RangeCallback :: Ptr CallbackData -> PAddr -> PAddr -> IO ()
cacheCleanL2RangeCallback _ _ _ = error "unimplemented"
