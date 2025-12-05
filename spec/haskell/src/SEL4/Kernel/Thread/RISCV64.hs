--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains the architecture-specific thread switch code for
-- RISCV 64bit.

module SEL4.Kernel.Thread.RISCV64 where

import SEL4.Machine
import SEL4.Model.StateData
import SEL4.Object.Structures
import SEL4.Kernel.VSpace.RISCV64
import {-# SOURCE #-} SEL4.Kernel.Init
import {-# SOURCE #-} SEL4.Object.TCB (asUser, threadGet)
import SEL4.Machine.RegisterSet.RISCV64(Register(..))

switchToThread :: PPtr TCB -> Kernel ()
switchToThread tcb = setVMRoot tcb

configureIdleThread :: PPtr TCB -> KernelInit ()
configureIdleThread _ = error "Unimplemented init code"

switchToIdleThread :: Kernel ()
switchToIdleThread = do
    stateAssert valid_idle'_asrt "`valid_idle'`"
    t <- getIdleThread
    setVMRoot t

activateIdleThread :: PPtr TCB -> Kernel ()
activateIdleThread _ = return ()

prepareNextDomain :: Kernel ()
prepareNextDomain = return ()
