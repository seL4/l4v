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

import SEL4.Machine
import SEL4.Machine.Hardware.RISCV64 as Arch hiding (PAddr, IRQ)
import SEL4.Object.Structures
import Data.Word (Word8, Word16, Word32)

{- RISC-V-Specific Objects -}

-- This data type enumerates the object invocations that are possible.
-- These are invocations on the page table structures, on pages, and on
-- ASID pool structures.

data Invocation
    = InvokeFIXMERISCV -- FIXME RISCV TODO
    deriving Show

{- FIXME RISCV total guess as to what will be needed
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
        ptMapPDE :: PDE,
        ptMapPDSlot :: PPtr PDE,
        ptMapVSpace :: PPtr PML4E }
    deriving Show

data PageInvocation
    = PageGetAddr {
        pageGetBasePtr :: PPtr Word }
    | PageRemap {
        pageRemapEntries :: (VMPageEntry, VMPageEntryPtr),
        pageRemapASID :: ASID,
        pageRemapVSpace :: PPtr PML4E }
    | PageMap {
        pageMapCap :: Capability,
        pageMapCTSlot :: PPtr CTE,
        pageMapEntries :: (VMPageEntry, VMPageEntryPtr),
        pageMapVSpace :: PPtr PML4E }
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
-}

{- Interrupt Control -}

data IRQControlInvocation
    = IssueIRQHandlerFIXMERISCV -- FIXME RISCV TODO
    deriving Show

{- Additional Register Subsets -}

-- The RISCV platform currently does not define any additional register sets
-- for the "CopyRegisters" operation. This may be changed in future to support
-- a floating point unit.

data CopyRegisterSets = RISCVNoExtraRegisters
    deriving Show
