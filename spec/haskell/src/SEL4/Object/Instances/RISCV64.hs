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

import SEL4.Machine.Hardware.RISCV64({-FIXME RISCV(..)-})
import SEL4.Object.Structures
import SEL4.Model
import Data.Helpers

-- FIXME RISCV TODO
