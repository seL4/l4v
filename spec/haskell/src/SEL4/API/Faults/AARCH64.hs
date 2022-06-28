--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

module SEL4.API.Faults.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Object.TCB(asUser)
import SEL4.Machine.Hardware.AARCH64(addressTranslateS1)
import SEL4.API.Failures.AARCH64
import Data.Bits

makeArchFaultMessage :: ArchFault -> PPtr TCB -> Kernel (Word, [Word])
makeArchFaultMessage (VMFault vptr archData) thread = do
    pc <- asUser thread getRestartPC
    return (5, pc:fromVPtr vptr:archData)
makeArchFaultMessage (VGICMaintenance archData) thread = do
    let msg = (case archData of
                   Nothing -> [-1]
                   Just idx -> [idx])
    return (6, msg)
makeArchFaultMessage (VCPUFault hsr) thread = return (7, [hsr])
makeArchFaultMessage (VPPIEvent irq) thread = return (8, [fromIntegral $ fromEnum $ irq])

handleArchFaultReply :: ArchFault -> PPtr TCB -> Word -> [Word] -> Kernel Bool
handleArchFaultReply (VMFault {}) _ _ _ = return True
handleArchFaultReply (VCPUFault {}) _ _ _ = return True
handleArchFaultReply (VPPIEvent {}) _ _ _ = return True
handleArchFaultReply (VGICMaintenance {}) _ _ _ = return True
