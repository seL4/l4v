--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
-- with minimal text substitution! Remove this comment after updating and
-- checking against C; update copyright as necessary.

module SEL4.API.Faults.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Object.TCB(asUser)
import SEL4.API.Failures.AARCH64

makeArchFaultMessage :: ArchFault -> PPtr TCB -> Kernel (Word, [Word])
makeArchFaultMessage (VMFault vptr archData) thread = do
    pc <- asUser thread getRestartPC
    return (5, pc:fromVPtr vptr:archData)

handleArchFaultReply :: ArchFault -> PPtr TCB -> Word -> [Word] -> Kernel Bool
handleArchFaultReply (VMFault {}) _ _ _ = return True
