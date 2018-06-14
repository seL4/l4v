-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

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
switchToThread tcb = do
    setVMRoot tcb
    bufferPtr <- threadGet tcbIPCBuffer tcb
    asUser tcb $ setRegister (Register TP) $ fromVPtr bufferPtr

configureIdleThread :: PPtr TCB -> KernelInit ()
configureIdleThread _ = error "Unimplemented init code"

switchToIdleThread :: Kernel ()
switchToIdleThread = do
    t <- getIdleThread
    setVMRoot t

activateIdleThread :: PPtr TCB -> Kernel ()
activateIdleThread _ = return ()
