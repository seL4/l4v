--
-- Copyright 2022, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains architecture-specific Domain management functions

module SEL4.Object.Domain.X64 where

import SEL4.Machine(PPtr)
import SEL4.Model
import SEL4.Object.Structures
import SEL4.API.Types
import SEL4.Object.FPU.X64

-- Save and clear any FPU state of a TCB before changing its domain, to ensure
-- that we do not later write to cross-domain state.

prepareSetDomain :: PPtr TCB -> Domain -> Kernel ()
prepareSetDomain t newDom = do
    curDom <- curDomain
    when (curDom /= newDom) (fpuRelease t)
