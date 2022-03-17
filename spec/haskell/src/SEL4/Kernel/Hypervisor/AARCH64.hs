--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

module SEL4.Kernel.Hypervisor.AARCH64 where

import SEL4.Machine (PPtr(..))
import SEL4.Model
import SEL4.Object.Structures
import SEL4.API.Failures
import SEL4.Kernel.FaultHandler
import SEL4.API.Failures.AARCH64
import SEL4.Machine.Hardware.AARCH64 (HypFaultType(..))

handleHypervisorFault :: PPtr TCB -> HypFaultType -> Kernel ()
handleHypervisorFault thread (ARMVCPUFault hsr) = do
    handleFault thread (ArchFault $ VCPUFault $ fromIntegral hsr)
