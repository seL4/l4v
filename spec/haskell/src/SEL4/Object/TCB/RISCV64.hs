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

import Prelude hiding (Word)
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

decodeTransfer :: Word8 -> KernelF SyscallError CopyRegisterSets
decodeTransfer _ = return RISCVNoExtraRegisters

performTransfer :: CopyRegisterSets -> PPtr TCB -> PPtr TCB -> Kernel ()
performTransfer _ _ _ = return ()

sanitiseRegister :: Bool -> Register -> Word -> Word
sanitiseRegister _ _ v = v

getSanitiseRegisterInfo :: PPtr TCB -> Kernel Bool
getSanitiseRegisterInfo _ = return False

setTCBIPCBuffer :: VPtr -> UserMonad ()
setTCBIPCBuffer ptr = setRegister (RegisterSet.Register TP) $ fromVPtr ptr

postModifyRegisters :: PPtr TCB -> PPtr TCB -> UserMonad ()
postModifyRegisters _ _ = return ()
