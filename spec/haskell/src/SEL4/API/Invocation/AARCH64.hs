--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the machine-specific invocations for RISC-V.

{-# LANGUAGE EmptyDataDecls #-}

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.
-- Progress: add VCPU invocations

module SEL4.API.Invocation.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Machine.Hardware.AARCH64 as Arch hiding (PAddr, IRQ)
import SEL4.API.InvocationLabels
import SEL4.API.InvocationLabels.AARCH64
import SEL4.Object.Structures
import Data.Word (Word8, Word16, Word32)
import SEL4.Machine.RegisterSet.AARCH64 (Register(..), VCPUReg(..))

{- RISC-V-Specific Objects -}

-- This data type enumerates the object invocations that are possible.
-- These are invocations on the page table structures, on pages, and on
-- ASID pool structures.

data Invocation
    = InvokeVSpaceRoot VSpaceRootInvocation
    | InvokePageTable PageTableInvocation
    | InvokePage PageInvocation
    | InvokeASIDControl ASIDControlInvocation
    | InvokeASIDPool ASIDPoolInvocation
    | InvokeVCPU VCPUInvocation
    deriving Show

data VSpaceRootInvocation
    = VSpaceRootNothing
    | VSpaceRootFlush {
        vsFlushType :: FlushType,
        vsFlushStart :: VPtr,
        vsFlushEnd :: VPtr,
        vsFlushPStart :: PAddr,
        vsFlushSpace :: PPtr PTE,
        vsFlushASID :: ASID }
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
    | PageFlush {
        pageFlushType :: FlushType,
        pageFlushStart :: VPtr,
        pageFlushEnd :: VPtr,
        pageFlushPStart :: PAddr,
        pageFlushSpace :: PPtr PTE,
        pageFlushASID :: ASID }
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

data FlushType
    = Clean | Invalidate | CleanInvalidate | Unify
    deriving Show

{- VCPUs -}

type HyperReg = VCPUReg
type HyperRegVal = Word

data VCPUInvocation
    = VCPUSetTCB (PPtr VCPU) (PPtr TCB)
    | VCPUInjectIRQ (PPtr VCPU) Int VIRQ
    | VCPUReadRegister (PPtr VCPU) HyperReg
    | VCPUWriteRegister (PPtr VCPU) HyperReg HyperRegVal
    | VCPUAckVPPI (PPtr VCPU) VPPIEventIRQ
    deriving (Show, Eq)

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

isVSpaceFlushLabel :: InvocationLabel -> Bool
isVSpaceFlushLabel x = case x of
      ArchInvocationLabel ARMVSpaceClean_Data -> True
      ArchInvocationLabel ARMVSpaceInvalidate_Data -> True
      ArchInvocationLabel ARMVSpaceCleanInvalidate_Data -> True
      ArchInvocationLabel ARMVSpaceUnify_Instruction -> True
      _ -> False

isPageFlushLabel :: InvocationLabel -> Bool
isPageFlushLabel x = case x of
      ArchInvocationLabel ARMPageClean_Data -> True
      ArchInvocationLabel ARMPageInvalidate_Data -> True
      ArchInvocationLabel ARMPageCleanInvalidate_Data -> True
      ArchInvocationLabel ARMPageUnify_Instruction -> True
      _ -> False
