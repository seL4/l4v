-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module defines instances of "PSpaceStorable" for architecture-specific
-- kernel objects. This includes page table and page directory entries, and
-- ASID pools.

module SEL4.Object.Instances.RISCV64 where

import SEL4.Machine.Hardware.RISCV64(PTE(..))
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

instance PSpaceStorable ASIDPool where
    makeObject = ASIDPool $
        funPartialArray (const Nothing) (0,bit asidLowBits - 1)
    injectKO = KOArch . KOASIDPool
    projectKO o = case o of
        KOArch (KOASIDPool e) -> return e
        _ -> typeError "ASID pool" o
