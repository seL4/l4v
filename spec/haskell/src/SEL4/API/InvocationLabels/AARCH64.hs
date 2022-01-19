--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the machine-specific invocations for RISCV 64bit.

{-# LANGUAGE EmptyDataDecls #-}

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.

module SEL4.API.InvocationLabels.AARCH64 where

data ArchInvocationLabel
        = RISCVPageTableMap
        | RISCVPageTableUnmap
        | RISCVPageMap
        | RISCVPageUnmap
        | RISCVPageGetAddress
        | RISCVASIDControlMakePool
        | RISCVASIDPoolAssign
        | RISCVIRQIssueIRQHandler
        deriving (Show, Eq, Enum, Bounded)
