--
-- Copyright 2014, General Dynamics C4 Systems
--
-- SPDX-License-Identifier: GPL-2.0-only
--

{-# LANGUAGE EmptyDataDecls, ForeignFunctionInterface, GeneralizedNewtypeDeriving #-}

module SEL4.Machine.Hardware.ARM.Callbacks where

import Prelude hiding (Word)
import SEL4.Machine.RegisterSet
import Foreign.Ptr
import Data.Bits
import Data.Word(Word8)


data CallbackData

type MachineData = Ptr CallbackData

newtype PAddr = PAddr { fromPAddr :: Word }
    deriving (Integral, Real, Show, Eq, Num, Bits, FiniteBits, Ord, Enum, Bounded)

plusPtr :: PAddr -> Int -> PAddr
plusPtr a b = a + (fromIntegral b)

foreign import ccall unsafe "qemu_load_word_phys"
    loadWordCallback :: Ptr CallbackData -> PAddr -> IO Word

foreign import ccall unsafe "qemu_store_word_phys"
    storeWordCallback :: Ptr CallbackData -> PAddr -> Word -> IO ()

foreign import ccall unsafe "qemu_tlb_flush"
    invalidateLocalTLBCallback :: Ptr CallbackData -> IO ()

foreign import ccall unsafe "qemu_tlb_flush_asid"
    invalidateLocalTLB_ASIDCallback :: Ptr CallbackData -> Word8 -> IO ()

foreign import ccall unsafe "qemu_tlb_flush_vptr"
    invalidateLocalTLB_VAASIDCallback :: Ptr CallbackData -> Word -> IO ()

foreign import ccall unsafe "qemu_set_asid"
    setHardwareASID :: Ptr CallbackData -> Word8 -> IO ()

-- FIXME qemu_set_root is still expecting the pointer, not its mangled
-- word version, per haskell-kernel-emulator/interface/callbacks.c
foreign import ccall unsafe "qemu_set_root"
    writeTTBR0 :: Ptr CallbackData -> Word -> IO ()

foreign import ccall unsafe "qemu_arm_get_ifsr"
    getIFSR :: Ptr CallbackData -> IO Word

foreign import ccall unsafe "qemu_arm_get_dfsr"
    getDFSR :: Ptr CallbackData -> IO Word

foreign import ccall unsafe "qemu_arm_get_far"
    getFAR :: Ptr CallbackData -> IO VPtr

