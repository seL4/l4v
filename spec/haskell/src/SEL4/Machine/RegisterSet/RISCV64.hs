--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the RISCV 64-bit register set.

{-# LANGUAGE FlexibleContexts #-}
module SEL4.Machine.RegisterSet.RISCV64 where

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

{- User-level Context -}

-- On RISC-V the representation of the user-level context of a thread is an array
-- of machine words, indexed by register name for the user registers.

data UserContext = UC { fromUC :: Array Register Word }
  deriving Show

-- A new user-level context is a list of values for the machine's registers.
-- Registers are generally initialised to 0, but there may be machine-specific
-- initial values for certain registers.

newContext :: UserContext
newContext = UC $ (funArray $ const 0)//initContext

-- Functions are provided to get and set a single register.

getRegister r = gets $ (! r) . fromUC

setRegister r v = modify $ UC . (//[(r, v)]) . fromUC
