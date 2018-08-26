-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module defines the machine-specific invocations for RISC-V.

{-# LANGUAGE EmptyDataDecls #-}

module SEL4.API.Invocation.RISCV64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Machine.Hardware.RISCV64 as Arch hiding (PAddr, IRQ)
import SEL4.Object.Structures
import Data.Word (Word8, Word16, Word32)

{- RISC-V-Specific Objects -}

-- This data type enumerates the object invocations that are possible.
-- These are invocations on the page table structures, on pages, and on
-- ASID pool structures.

data Invocation
    = InvokePageTable PageTableInvocation
    | InvokePage PageInvocation
    | InvokeASIDControl ASIDControlInvocation
    | InvokeASIDPool ASIDPoolInvocation
    deriving Show

data PageTableInvocation
    = PageTableUnmap {
        ptUnmapCap :: ArchCapability,
        ptUnmapCapSlot :: PPtr CTE }
    | PageTableMap {
        ptMapCap :: Capability,
        ptMapCTSlot :: PPtr CTE,
        ptMapPTE :: PTE,
        ptMapPTSlot :: PPtr PTE }
    deriving Show

data PageInvocation
    = PageGetAddr {
        pageGetBasePtr :: PPtr Word }
    | PageRemap {
        pageRemapEntries :: (PTE, PPtr PTE) }
    | PageMap {
        pageMapCap :: Capability,
        pageMapCTSlot :: PPtr CTE,
        pageMapEntries :: (PTE, PPtr PTE) }
    | PageUnmap {
        pageUnmapCap :: ArchCapability,
        pageUnmapCapSlot :: PPtr CTE }
    deriving Show

data ASIDControlInvocation
    = MakePool {
        makePoolFrame :: PPtr (),
        makePoolSlot :: PPtr CTE,
        makePoolParent :: PPtr CTE,
        makePoolBase :: ASID }
    deriving Show

data ASIDPoolInvocation
    = Assign {
        assignASID :: ASID,
        assignASIDPool :: PPtr ASIDPool,
        assignASIDCTSlot :: PPtr CTE }
    deriving Show

{- Interrupt Control -}

-- on current RISCV platforms, we do not have proper interrupts

data IRQControlInvocation
    = RISCVNoIRQControlInvocation
    deriving Show

{- Additional Register Subsets -}

-- The RISCV platform currently does not define any additional register sets
-- for the "CopyRegisters" operation. This may be changed in future to support
-- a floating point unit.

data CopyRegisterSets = RISCVNoExtraRegisters
    deriving Show
