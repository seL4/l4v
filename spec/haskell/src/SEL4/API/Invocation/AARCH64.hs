--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the machine-specific invocations for AARCH64.

{-# LANGUAGE EmptyDataDecls #-}

module SEL4.API.Invocation.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Machine.Hardware.AARCH64 as Arch hiding (PAddr, IRQ)
import SEL4.API.InvocationLabels
import SEL4.API.InvocationLabels.AARCH64
import SEL4.Object.Structures
import Data.Word (Word8, Word16, Word32)
import SEL4.Machine.RegisterSet.AARCH64 (Register(..), VCPUReg(..))

{- AARCH64-Specific Objects -}

-- This data type enumerates the object invocations that are possible.

data Invocation
    = InvokeVSpace VSpaceInvocation
    | InvokePageTable PageTableInvocation
    | InvokePage PageInvocation
    | InvokeASIDControl ASIDControlInvocation
    | InvokeASIDPool ASIDPoolInvocation
    | InvokeVCPU VCPUInvocation
    | InvokeSGISignal SGISignalInvocation
    | InvokeSMCCall SMCInvocation
    deriving Show

data VSpaceInvocation
    = VSpaceNothing
    | VSpaceFlush {
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
        pageMapCap :: ArchCapability,
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

{- SGI -}

data SGISignalInvocation
    = SGISignalGenerate {
        sgiIRQ :: Word,
        sgiTargets :: Word }
    deriving (Show, Eq)

{- SMC -}

data SMCInvocation
    = SMCCall {
        smcArgs :: EightTuple Word }
    deriving (Show, Eq)

{- Interrupt Control -}

data IRQControlInvocation
    = IssueIRQHandler {
        issueHandlerIRQ :: IRQ,
        issueHandlerSlot,
        issueHandlerControllerSlot :: PPtr CTE,
        issueHandlerTrigger :: Bool }
    | IssueSGISignal {
        issueSGIIRQ :: Word,
        issueSGITargets :: Word,
        issueSGIControlSlot,
        issueSGISlot :: PPtr CTE }
    deriving (Show, Eq)

{- Additional Register Subsets -}

-- The AArch64 platform currently does not define any additional register sets
-- for the "CopyRegisters" operation. This may be changed in future to support
-- a floating point unit.

data CopyRegisterSets = ARMNoExtraRegisters
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
