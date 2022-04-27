--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines instances of "PSpaceStorable" for architecture-specific
-- kernel objects. This includes page table entries, VCPUs and ASID pools.

module SEL4.Object.Instances.AARCH64 where

import SEL4.Machine.Hardware.AARCH64(PTE(..))
import SEL4.Object.Structures
import SEL4.Model
import Data.Helpers
import Data.Bits

instance PSpaceStorable PTE where
    makeObject = InvalidPTE
    injectKO = KOArch . KOPTE
    projectKO o = case o of
                KOArch (KOPTE p) -> return p
                _ -> typeError "PTE" o

instance PSpaceStorable VCPU where
    makeObject = makeVCPUObject
    injectKO = KOArch . KOVCPU
    projectKO o = case o of
                KOArch (KOVCPU p) -> return p
                _ -> typeError "VCPU" o

instance PSpaceStorable ASIDPool where
    makeObject = ASIDPool $
        funPartialArray (const Nothing) (0,bit asidLowBits - 1)
    injectKO = KOArch . KOASIDPool
    projectKO o = case o of
        KOArch (KOASIDPool e) -> return e
        _ -> typeError "ASID pool" o
