-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module contains architecture-specific TCB management functions.
-- Specifically, these functions are used by the "CopyRegisters" operation to
-- transfer architecture-specific subsets of the register set.

-- There are presently no RISC-V-specific register subsets defined, but in
-- future this may be extended to transfer floating point registers and other
-- coprocessor state.

module SEL4.Object.TCB.RISCV64 where

import SEL4.Machine(PPtr)
import SEL4.Model
import SEL4.Object.Structures
import SEL4.API.Failures
import SEL4.API.Invocation.RISCV64
import SEL4.Machine.RegisterSet(setRegister, UserMonad, VPtr(..))
import qualified SEL4.Machine.RegisterSet as RegisterSet(Register(..))
import SEL4.Machine.RegisterSet.RISCV64(Register(..), Word)
import Data.Bits

import Data.Word(Word8)

-- FIXME RISCV unchecked copypasta
decodeTransfer :: Word8 -> KernelF SyscallError CopyRegisterSets
decodeTransfer _ = return RISCVNoExtraRegisters

-- FIXME RISCV unchecked copypasta
performTransfer :: CopyRegisterSets -> PPtr TCB -> PPtr TCB -> Kernel ()
performTransfer _ _ _ = return ()

sanitiseRegister :: Bool -> Register -> Word -> Word
sanitiseRegister _ r v = error "FIXME RISCV TODO"

-- FIXME RISCV unchecked copypasta
getSanitiseRegisterInfo :: PPtr TCB -> Kernel Bool
getSanitiseRegisterInfo _ = return False

-- FIXME RISCV unchecked copypasta
setTCBIPCBuffer :: VPtr -> UserMonad ()
setTCBIPCBuffer ptr = return ()

-- Here, cur = ksCurThread

-- FIXME RISCV unchecked copypasta
postModifyRegisters :: PPtr TCB -> PPtr TCB -> UserMonad ()
postModifyRegisters cur dest =
    when (dest /= cur) $ setRegister (RegisterSet.Register ErrorRegister) 0
