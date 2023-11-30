--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the machine-specific invocations for AArch 64bit.

{-# LANGUAGE EmptyDataDecls #-}

module SEL4.API.InvocationLabels.AARCH64 where

data ArchInvocationLabel
        = ARMVSpaceClean_Data
        | ARMVSpaceInvalidate_Data
        | ARMVSpaceCleanInvalidate_Data
        | ARMVSpaceUnify_Instruction
        | ARMSMCCall
        | ARMPageTableMap
        | ARMPageTableUnmap
        | ARMPageMap
        | ARMPageUnmap
        | ARMPageClean_Data
        | ARMPageInvalidate_Data
        | ARMPageCleanInvalidate_Data
        | ARMPageUnify_Instruction
        | ARMPageGetAddress
        | ARMASIDControlMakePool
        | ARMASIDPoolAssign
        | ARMVCPUSetTCB
        | ARMVCPUInjectIRQ
        | ARMVCPUReadReg
        | ARMVCPUWriteReg
        | ARMVCPUAckVPPI
        | ARMIRQIssueIRQHandlerTrigger
        -- TODO AARCH64: SMMU invocation labels in C
        -- ARMSIDIssueSIDManager,
        -- | ARMSIDGetFault
        -- | ARMSIDClearFault
        -- | ARMSIDBindCB
        -- | ARMSIDUnbindCB
        -- | ARMCBIssueCBManager
        -- | ARMCBTLBInvalidateAll
        -- | ARMCBAssignVspace
        -- | ARMCBUnassignVspace
        -- | ARMCBTLBInvalidate
        -- | ARMCBGetFault
        -- | ARMCBClearFault
        deriving (Show, Eq, Enum, Bounded)
