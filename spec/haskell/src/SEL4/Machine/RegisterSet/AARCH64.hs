--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the RISCV 64-bit register set.

{-# LANGUAGE FlexibleContexts #-}
-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.

module SEL4.Machine.RegisterSet.AARCH64 where

import Prelude hiding (Word)
import qualified Data.Word
import Data.Array
import Data.Bits
import Data.Helpers

import Control.Monad.State(State, gets, modify)

data Register
    = LR -- "RA"
    | SP | GP
    | S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 | S10 | S11
    | A0 | A1 | A2 | A3 | A4 | A5 | A6 | A7
    | T0 | T1 | T2 | T3 | T4 | T5 | T6 | TP
    | SPSR_EL1 -- FIXME AARCH64: this is only so haskell compiles
    | SCAUSE | SSTATUS | FaultIP | NextIP
    deriving (Eq, Enum, Bounded, Ord, Ix, Show)

type Word = Data.Word.Word64

capRegister :: Register
capRegister = A0

msgInfoRegister :: Register
msgInfoRegister = A1

msgRegisters :: [Register]
msgRegisters = [A2 .. A5]

badgeRegister :: Register
badgeRegister = A0

frameRegisters :: [Register]
frameRegisters = FaultIP : LR : SP : GP : [S0 .. S11]

gpRegisters :: [Register]
gpRegisters = [A0 .. A7] ++ [T0 .. T6] ++ [TP]

exceptionMessage :: [Register]
exceptionMessage = [FaultIP, SP]

syscallMessage :: [Register]
syscallMessage = FaultIP : SP : LR : [A0 .. A6]

tlsBaseRegister :: Register
tlsBaseRegister = TP

sstatusSPIE :: Word
sstatusSPIE = 0x20

initContext :: [(Register, Word)]
initContext = [ (SSTATUS , sstatusSPIE) ]

faultRegister :: Register
faultRegister = FaultIP

nextInstructionRegister :: Register
nextInstructionRegister = NextIP

{- VCPU-saved Registers -}

data VCPUReg =
      VCPURegSCTLR
    | VCPURegTTBR0
    | VCPURegTTBR1
    | VCPURegTCR
    | VCPURegMAIR
    | VCPURegAMAIR
    | VCPURegCIDR
    | VCPURegACTLR
    | VCPURegCPACR
    | VCPURegAFSR0
    | VCPURegAFSR1
    | VCPURegESR
    | VCPURegFAR
    | VCPURegISR
    | VCPURegVBAR
    | VCPURegTPIDR_EL1
    | VCPURegSP_EL1
    | VCPURegELR_EL1
    | VCPURegSPSR_EL1
    | VCPURegCNTV_CTL
    | VCPURegCNTV_CVAL
    | VCPURegCNTVOFF
    | VCPURegCNTKCTL_EL1
    deriving (Eq, Enum, Bounded, Ord, Ix, Show)

vcpuRegNum :: Int
vcpuRegNum = fromEnum (maxBound :: VCPUReg)

vcpuRegSavedWhenDisabled :: VCPUReg -> Bool
vcpuRegSavedWhenDisabled VCPURegSCTLR = True
vcpuRegSavedWhenDisabled VCPURegCNTV_CTL = True
vcpuRegSavedWhenDisabled VCPURegCPACR = True
vcpuRegSavedWhenDisabled _ = False

{- User-level Context -}

-- The FPU state consists of an array of 64 general registers, as well as special
-- registers. We use an array for the general registers, with the convention that
-- all unused entries map to 0.
data FPUState = FPUState { fpuRegs :: Array Int Data.Word.Word64
                         , fpuSr :: Data.Word.Word32
                         , fpuCr :: Data.Word.Word32 }
  deriving Show

-- The representation of the user-level context of a thread is an array of
-- machine words, indexed by register name for the user registers, plus the
-- state of the FPU. There are no operations on the FPU state apart from save
-- and restore at kernel entry and exit.
data UserContext = UC { fromUC :: Array Register Word,
                        fpuState :: FPUState }
  deriving Show

-- A new user-level context is a list of values for the machine's registers.
-- Registers are generally initialised to 0, but there may be machine-specific
-- initial values for certain registers. The FPU state is zeroed.

newFPUState :: FPUState
newFPUState = FPUState (funPartialArray (const 0) (0,63)) 0 0

newContext :: UserContext
newContext = UC ((funArray $ const 0)//initContext) newFPUState

-- Functions are provided to get and set a single register.

getRegister r = gets $ (!r) . fromUC

setRegister r v = modify (\ uc -> UC (fromUC uc //[(r, v)]) (fpuState uc))
