--
-- Copyright 2022, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains architecture-specific Domain management functions

{-# LANGUAGE CPP #-}

module SEL4.Object.Domain.ARM where

import SEL4.Machine(PPtr)
import SEL4.Model
import SEL4.Object.Structures
import SEL4.API.Types

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
import SEL4.Object.VCPU.ARM
#endif

-- Save and clear any VCPU state of a TCB before changing its domain, to ensure
-- that we do not later write to cross-domain state.

prepareSetDomain :: PPtr TCB -> Domain -> Kernel ()
prepareSetDomain t newDom = do
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
    curDom <- curDomain
    when (curDom /= newDom) (vcpuFlushIfCurrent t)
#else
    return ()
#endif
