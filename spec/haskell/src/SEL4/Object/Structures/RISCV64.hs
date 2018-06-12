-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module contains the physical memory model's representations of the
-- RISC-V 64bit-specific data structures, as well as a type representing a capability to
-- a RISC-V-specific object.

{-# LANGUAGE EmptyDataDecls, GeneralizedNewtypeDeriving #-}

module SEL4.Object.Structures.RISCV64 where

import SEL4.Machine.RegisterSet
import SEL4.Machine.Hardware.RISCV64
import Data.Array
import Data.Bits
import Data.Word(Word64)

{- Capabilities -}

data ArchCapability -- FIXME RISCV TODO
    = ASIDControlCap
    deriving (Eq, Show)

{- Kernel Objects -}

data ArchKernelObject -- FIXME RISCV TODO
    = FIXMERISCVArchKernelObject
    deriving Show

archObjSize ::  ArchKernelObject -> Int
archObjSize a = error "FIXME RISCV TODO"

{- Threads -}

-- FIXME RISCV unchecked copypasta
data ArchTCB = ArchThread {
        atcbContext :: UserContext }
    deriving Show

newArchTCB = ArchThread {
    atcbContext = newContext }

atcbContextSet :: UserContext -> ArchTCB -> ArchTCB
atcbContextSet uc atcb = atcb { atcbContext = uc }

atcbContextGet :: ArchTCB -> UserContext
atcbContextGet = atcbContext

{- ASID Pools -}

-- FIXME RISCV unchecked copypasta
newtype ASID = ASID { fromASID :: Word64 }
    deriving (Show, Eq, Ord, Enum, Real, Integral, Num, Bits, Ix, Bounded)

-- FIXME RISCV TODO
