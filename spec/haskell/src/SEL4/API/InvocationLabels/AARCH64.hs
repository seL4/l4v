--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the machine-specific invocations for AArch 64bit.

{-# LANGUAGE EmptyDataDecls #-}

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.
-- Progress: renamed RISCV->ARM in labels, added VCPU invocations

module SEL4.API.InvocationLabels.AARCH64 where

-- FIXME AARCH64: review enum arch_invocation_label in C, the list is quite
-- different between ARM and RISCV64
data ArchInvocationLabel
        = ARMVSpaceClean_Data
        | ARMVSpaceInvalidate_Data
        | ARMVSpaceCleanInvalidate_Data
        | ARMVSpaceUnify_Instruction
        | ARMPageTableMap
        | ARMPageTableUnmap
        | ARMPageMap
        | ARMPageUnmap
        | ARMPageGetAddress
        | ARMPageClean_Data
        | ARMPageInvalidate_Data
        | ARMPageCleanInvalidate_Data
        | ARMPageUnify_Instruction
        | ARMASIDControlMakePool
        | ARMASIDPoolAssign
        | ARMVCPUSetTCB
        | ARMVCPUInjectIRQ
        | ARMVCPUReadReg
        | ARMVCPUWriteReg
        | ARMVCPUAckVPPI
        | ARMIRQIssueIRQHandler
        deriving (Show, Eq, Enum, Bounded)
