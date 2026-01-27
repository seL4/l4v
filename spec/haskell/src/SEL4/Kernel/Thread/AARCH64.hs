--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains the architecture-specific thread switch code for
-- AArch64.

module SEL4.Kernel.Thread.AARCH64 where

import SEL4.Machine
import SEL4.Model.StateData
import SEL4.Model.PSpace (getObject)
import SEL4.Object.Structures
import SEL4.Kernel.VSpace.AARCH64
import {-# SOURCE #-} SEL4.Kernel.Init
import {-# SOURCE #-} SEL4.Object.TCB (asUser, threadGet)
import SEL4.Machine.RegisterSet.AARCH64(Register(..))
import SEL4.Object.VCPU.AARCH64
import SEL4.Object.FPU.AARCH64

switchToThread :: PPtr TCB -> Kernel ()
switchToThread tcb = do
    tcbobj <- getObject tcb
    vcpuSwitch (atcbVCPUPtr $ tcbArch tcbobj)
    setVMRoot tcb
    lazyFpuRestore tcb

configureIdleThread :: PPtr TCB -> KernelInit ()
configureIdleThread _ = error "Unimplemented init code"

switchToIdleThread :: Kernel ()
switchToIdleThread = do
    vcpuSwitch Nothing
    setGlobalUserVSpace

activateIdleThread :: PPtr TCB -> Kernel ()
activateIdleThread _ = return ()

prepareNextDomain :: Kernel ()
prepareNextDomain = do
    vcpuFlush
    switchLocalFpuOwner Nothing
