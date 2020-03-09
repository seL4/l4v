--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- The RISCV target does not have any hypervisor support.

module SEL4.Kernel.Hypervisor.RISCV64 where

import SEL4.Machine (PPtr(..))
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Machine.Hardware.RISCV64 (HypFaultType(..))

handleHypervisorFault :: PPtr TCB -> HypFaultType -> Kernel ()
handleHypervisorFault _ (RISCVNoHypFaults) = return ()
