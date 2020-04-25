--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

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

-- The RISCV platform requires an interrupt control call to record whether
-- the interrupt was edge or level-triggered.

data IRQControlInvocation
    = IssueIRQHandler {
        issueHandlerIRQ :: IRQ,
        issueHandlerSlot,
        issueHandlerControllerSlot :: PPtr CTE,
        issueHandlerTrigger :: Bool }
    deriving (Show, Eq)

{- Additional Register Subsets -}

-- The RISCV platform currently does not define any additional register sets
-- for the "CopyRegisters" operation. This may be changed in future to support
-- a floating point unit.

data CopyRegisterSets = RISCVNoExtraRegisters
    deriving Show
