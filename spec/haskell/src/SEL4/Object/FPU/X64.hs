--
-- Copyright 2024, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

{-# LANGUAGE CPP #-}

module SEL4.Object.FPU.X64 where

import SEL4.Machine
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Machine.Hardware.X64
import SEL4.Machine.RegisterSet.X64
import SEL4.Model.StateData.X64
import {-# SOURCE #-} SEL4.Object.TCB(asUser, threadGet)

import Data.Bits
import Data.Maybe

saveFpuState :: PPtr TCB -> Kernel ()
saveFpuState tcbPtr = do
    fpuState <- doMachineOp readFpuState
    asUser tcbPtr (setFPUState fpuState)

loadFpuState :: PPtr TCB -> Kernel ()
loadFpuState tcbPtr = do
    fpuState <- asUser tcbPtr getFPUState
    doMachineOp (writeFpuState fpuState)

switchLocalFpuOwner :: Maybe (PPtr TCB) -> Kernel ()
switchLocalFpuOwner newOwner = do
    doMachineOp enableFpu
    curFpuOwner <- gets (x64KSCurFPUOwner . ksArchState)
    maybe (return ()) saveFpuState curFpuOwner
    case newOwner of
        Nothing -> doMachineOp disableFpu
        Just tcbPtr -> loadFpuState tcbPtr
    modifyArchState (\s -> s { x64KSCurFPUOwner = newOwner })

fpuRelease :: PPtr TCB -> Kernel ()
fpuRelease tcbPtr = do
    curFpuOwner <- gets (x64KSCurFPUOwner . ksArchState)
    when (curFpuOwner /= Just tcbPtr) (switchLocalFpuOwner Nothing)

lazyFpuRestore :: PPtr TCB -> Kernel ()
lazyFpuRestore tcbPtr = do
    flags <- threadGet tcbFlags tcbPtr
    if (isFlagSet (ArchFlag FpuDisabled) flags)
      then doMachineOp disableFpu
      else do
          doMachineOp enableFpu
          switchLocalFpuOwner (Just tcbPtr)
