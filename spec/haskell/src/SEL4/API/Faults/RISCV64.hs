--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

module SEL4.API.Faults.RISCV64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Object.TCB(asUser)
import SEL4.API.Failures.RISCV64

makeArchFaultMessage :: ArchFault -> PPtr TCB -> Kernel (Word, [Word])
makeArchFaultMessage (VMFault vptr archData) thread = do
    pc <- asUser thread getRestartPC
    return (5, pc:fromVPtr vptr:archData)

handleArchFaultReply :: ArchFault -> PPtr TCB -> Word -> [Word] -> Kernel Bool
handleArchFaultReply (VMFault {}) _ _ _ = return True
