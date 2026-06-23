--
-- Copyright 2022, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains architecture-specific Domain management functions

module SEL4.Object.Domain.RISCV64 where

import SEL4.Machine(PPtr)
import SEL4.Model
import SEL4.Object.Structures
import SEL4.API.Types

-- No arch-specific operations needed before changing the domain of a TCB on
-- RISC-V.

prepareSetDomain :: PPtr TCB -> Domain -> Kernel ()
prepareSetDomain t newDom = return ()
