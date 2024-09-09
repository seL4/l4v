--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains architecture-specific TCB management functions.
-- Specifically, these functions are used by the "CopyRegisters" operation to
-- transfer architecture-specific subsets of the register set.

-- There are presently no AArch64-specific register subsets defined, but in
-- future this may be extended to transfer floating point registers and other
-- coprocessor state.

module SEL4.Object.TCB.AARCH64 where

import Prelude hiding (Word)
import SEL4.Machine(PPtr)
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Object.Instances()
import SEL4.API.Types
import SEL4.API.Failures
import SEL4.API.Invocation.AARCH64
import SEL4.Machine.RegisterSet(setRegister, UserMonad, VPtr(..))
import qualified SEL4.Machine.RegisterSet as RegisterSet(Register(..))
import SEL4.Machine.RegisterSet.AARCH64(Register(..), Word)
import SEL4.Object.FPU.AARCH64
import Data.Bits
import Data.Maybe
import Data.Word(Word8)

decodeTransfer :: Word8 -> KernelF SyscallError CopyRegisterSets
decodeTransfer _ = return ARMNoExtraRegisters

performTransfer :: CopyRegisterSets -> PPtr TCB -> PPtr TCB -> Kernel ()
performTransfer _ _ _ = return ()

sanitiseRegister :: Bool -> Register -> Word -> Word
sanitiseRegister b SPSR_EL1 v =
  if (b && ((v .&. 0x1f) `elem` modes))
      then v
      else v'
  where v' = (v .&. 0xf0000000) .|. 0x140
        modes = [0, 4, 5]
sanitiseRegister _ _ v = v

getSanitiseRegisterInfo :: PPtr TCB -> Kernel Bool
getSanitiseRegisterInfo t = do
   v <- liftM (atcbVCPUPtr . tcbArch) $ getObject t
   return $ isJust v

postModifyRegisters :: PPtr TCB -> PPtr TCB -> UserMonad ()
postModifyRegisters _ _ = return ()

postSetFlags :: PPtr TCB -> TcbFlags -> Kernel ()
postSetFlags t flags =
    when (isFlagSet FpuDisabled flags) (fpuRelease t)
