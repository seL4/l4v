-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module defines the RISCV 64-bit register set.

module SEL4.Machine.RegisterSet.RISCV64 where

import qualified Data.Word
import Data.Array
import Data.Bits
import Data.Helpers

import Control.Monad.State(State, gets, modify)

data Register = FIXMERISCVreg -- FIXME RISCV TODO fill in and order properly
    | ErrorRegister
    deriving (Eq, Enum, Bounded, Ord, Ix, Show)

type Word = Data.Word.Word64

capRegister = error "FIXME RISCV TODO"
msgInfoRegister = error "FIXME RISCV TODO"
msgRegisters = error "FIXME RISCV TODO"
badgeRegister = error "FIXME RISCV TODO"
frameRegisters = error "FIXME RISCV TODO"
gpRegisters = error "FIXME RISCV TODO"
exceptionMessage = error "FIXME RISCV TODO"

syscallMessage = error "FIXME RISCV TODO"

initContext :: [(Register, Word)]
initContext = error "FIXME RISCV TODO"

{- User-level Context -}

-- On RISC-V the representation of the user-level context of a thread is an array
-- of machine words, indexed by register name for the user registers, plus FIXME RISCV FPU?

-- FIXME RISCV unchecked copypasta
data UserContext = UC { fromUC :: Array Register Word }
  deriving Show

-- A new user-level context is a list of values for the machine's registers.
-- Registers are generally initialised to 0, but there may be machine-specific
-- initial values for certain registers.

newContext :: UserContext
newContext = error "FIXME RISCV TODO"

-- Functions are provided to get and set a single register.

getRegister r = gets $ (!r) . fromUC

setRegister r v = error "FIXME RISCV TODO"
