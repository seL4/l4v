-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- The RISCV target does not have any hypervisor support.

module SEL4.Kernel.Hypervisor.RISCV64 where

import SEL4.Machine (PPtr(..))
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Machine.Hardware.RISCV64 (HypFaultType(..))

handleHypervisorFault :: PPtr TCB -> HypFaultType -> Kernel ()
handleHypervisorFault _ (RISCVNoHypFaults) = return ()
