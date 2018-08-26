-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

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
