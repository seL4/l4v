--
-- Copyright 2014, General Dynamics C4 Systems
--
-- SPDX-License-Identifier: GPL-2.0-only
--

{-# LANGUAGE EmptyDataDecls, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}

module SEL4.Machine.Hardware.X64.PC99 where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet
import Foreign.Ptr
import Data.Bits
import Data.Word(Word8, Word16, Word64)
import Data.Ix

data CallbackData

newtype IRQ = IRQ Word8
    deriving (Enum, Ord, Ix, Eq, Show)

instance Bounded IRQ where
    minBound = IRQ 0
    maxBound = IRQ 31

newtype PAddr = PAddr { fromPAddr :: Word }
    deriving (Integral, Real, Show, Eq, Num, Bits, FiniteBits, Ord, Enum, Bounded)


pptrUserTop :: VPtr
pptrUserTop = VPtr 0x00007fffffffffff

paddrBase :: PAddr
paddrBase = PAddr 0x0

pptrBase :: VPtr
pptrBase = VPtr 0xffffff8000000000

pptrTop :: VPtr
pptrTop = VPtr 0xffffffff80000000

kernelELFPAddrBase :: PAddr
kernelELFPAddrBase = PAddr 0x00100000

kernelELFBase :: VPtr
kernelELFBase = VPtr $ fromVPtr pptrTop + (fromPAddr kernelELFPAddrBase)

pageColourBits :: Int
pageColourBits = 0 -- qemu has no cache

getMemoryRegions :: Ptr CallbackData -> IO [(PAddr, PAddr)]
getMemoryRegions _ = return [(0, 0x8 `shiftL` 24)]

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

-- We don't need to acknowledge interrupts explicitly because we don't use
-- the vectored interrupt controller.
ackInterrupt :: Ptr CallbackData -> IRQ -> IO ()
ackInterrupt _ _ = return ()

foreign import ccall unsafe "qemu_run_devices"
    runDevicesCallback :: IO ()

interruptCallback :: Ptr CallbackData -> IO (Maybe IRQ)
interruptCallback env = do
    -- No need to call back to the simulator here; we just check the PIC's
    -- active interrupt register. This will probably work for real ARMs too,
    -- as long as we're not using vectored interrupts
    active <- loadWordCallback env (avicAddr + 64)
    return $ if active == 0xFFFF0000
        then Nothing
        else (Just $ IRQ $ fromIntegral (active `shiftR` 16))

getActiveIRQ :: Ptr CallbackData -> IO (Maybe IRQ)
getActiveIRQ env = do
    runDevicesCallback
    interruptCallback env

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

resetTimer :: Ptr CallbackData -> IO ()
resetTimer env = storeWordCallback env (timerAddr+0x4) 1

foreign import ccall unsafe "qemu_load_word_phys"
    loadWordCallback :: Ptr CallbackData -> PAddr -> IO Word

foreign import ccall unsafe "qemu_store_word_phys"
    storeWordCallback :: Ptr CallbackData -> PAddr -> Word -> IO ()

-- PC99 stubs

writeCR3 = error "Unimplemented"

invalidateTLB = error "Unimplemented"
mfence = error "Unimplemented"
invalidateASID = error "Unimplemented"
invalidateTranslationSingleASID = error "Unimplemented"

invalidateLocalPageStructureCacheASID :: PAddr -> Word64 -> IO ()
invalidateLocalPageStructureCacheASID = error "Unimplemented"

nativeThreadUsingFPU :: Word -> IO Bool
nativeThreadUsingFPU = error "Unimplemented"

switchFpuOwner :: Word -> Word -> IO ()
switchFpuOwner = error "Unimplemented"

getFaultAddress :: Ptr CallbackData -> IO VPtr
getFaultAddress _ = error "Unimplemented" -- FIXME: should read CR2

firstValidIODomain :: Word16
firstValidIODomain = error "Unimplemented"

numIODomainIDBits :: Int
numIODomainIDBits = error "Unimplemented"

minUserIRQ :: IRQ
minUserIRQ = IRQ 0x10 -- irq_user_min in C

maxUserIRQ :: IRQ
maxUserIRQ = IRQ 0x7B -- irq_user_max in C

irqIntOffset :: Word
irqIntOffset = 0x20 -- IRQ_INT_OFFSET in C

maxPCIBus :: Word
maxPCIBus = 255 -- PCI_BUS_MAX

maxPCIDev :: Word
maxPCIDev = 31 -- PCI_DEV_MAX

maxPCIFunc :: Word
maxPCIFunc = 7 -- PCI_FUNC_MAX

ioapicIRQLines :: Word
ioapicIRQLines = 24 -- IOAPIC_IRQ_LINES

-- error checks this performs moved out to x64 decodeIRQControl
ioapicMapPinToVector :: Ptr CallbackData -> Word -> Word -> Word -> Word -> Word -> IO ()
ioapicMapPinToVector = error "Unimplemented"

