--
-- Copyright 2022, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the AArch 64-bit register set.

{-# LANGUAGE FlexibleContexts #-}

module SEL4.Machine.RegisterSet.AARCH64 where

import Prelude hiding (Word)
import qualified Data.Word
import Data.Array
import Data.Bits
import Data.Helpers

import Control.Monad.State(State, gets, modify)

-- note on aliases: NextIP = ELR_EL1, X30 = LR, TPIDR_EL0 = TLS_BASE
data Register
    = X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9
    | X10 | X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19
    | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30
    | SP_EL0 | NextIP | SPSR_EL1 | FaultIP | TPIDR_EL0 | TPIDRRO_EL0
    deriving (Eq, Enum, Bounded, Ord, Ix, Show)

type Word = Data.Word.Word64

capRegister :: Register
capRegister = X0

msgInfoRegister :: Register
msgInfoRegister = X1

msgRegisters :: [Register]
msgRegisters = [X2 .. X5]

badgeRegister :: Register
badgeRegister = X0

frameRegisters :: [Register]
frameRegisters = FaultIP : SP_EL0 : SPSR_EL1 : [X0 .. X8] ++ [X16, X17, X18, X29, X30]

gpRegisters :: [Register]
gpRegisters = [X9 .. X15] ++ [X19 .. X28] ++ [TPIDR_EL0, TPIDRRO_EL0]

exceptionMessage :: [Register] -- see fault_messages[] in C
exceptionMessage = [FaultIP, SP_EL0, SPSR_EL1]

syscallMessage :: [Register] -- see fault_messages[] in C; note NextIP = ELR_EL1
syscallMessage = [X0 .. X7] ++ [FaultIP, SP_EL0, NextIP, SPSR_EL1]

tlsBaseRegister :: Register
tlsBaseRegister = TPIDR_EL0

pstateUser :: Word
pstateUser =  0x140 -- PSTATE_USER

initContext :: [(Register, Word)]
initContext = [ (SPSR_EL1 , pstateUser) ]

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
    | VCPURegVMPIDR_EL2
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
                           -- fpsr and fpcr in C
                         , fpuSr :: Data.Word.Word32
                         , fpuCr :: Data.Word.Word32 }
  deriving Show

-- The representation of the user-level context of a thread is an array of
-- machine words, indexed by register name for the user registers, plus the
-- state of the FPU.
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

-- Functions are provided to get and set a single register, or to get and set the FPU state.

getRegister r = gets $ (! r) . fromUC

setRegister r v = modify (\ uc -> UC (fromUC uc //[(r, v)]) (fpuState uc))

getFPUState :: State UserContext FPUState
getFPUState = gets fpuState

setFPUState fc = modify (\ uc -> UC (fromUC uc) fc)
