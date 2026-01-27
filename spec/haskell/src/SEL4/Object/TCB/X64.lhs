%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains x64-specific TCB management functions. Specifically, these functions are used by the "CopyRegisters" operation to transfer x64-specific subsets of the register set.

There are presently no x64-specific register subsets defined, but in future this may be extended to transfer floating point registers and other coprocessor state.

%FIXME: add x64 floating point registers + any extra state

> module SEL4.Object.TCB.X64 where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine(PPtr)
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Invocation.X64
> import SEL4.Machine.RegisterSet(setRegister, UserMonad, VPtr(..))
> import qualified SEL4.Machine.RegisterSet as RegisterSet(Register(..))
> import SEL4.Machine.RegisterSet.X64(Register(..), Word)
> import SEL4.Object.FPU.X64
> import Data.Bits

> import Data.Word(Word8)

\end{impdetails}

> decodeTransfer :: Word8 -> KernelF SyscallError CopyRegisterSets
> decodeTransfer _ = return X64NoExtraRegisters

> performTransfer :: CopyRegisterSets -> PPtr TCB -> PPtr TCB -> Kernel ()
> performTransfer _ _ _ = return ()

> sanitiseOrFlags :: Word
> sanitiseOrFlags = bit 1 .|. bit 9

> sanitiseAndFlags :: Word
> sanitiseAndFlags = (bit 12 - 1) .&. (complement (bit 3)) .&. (complement (bit 5)) .&. (complement (bit 8)) -- should be 0x111011010111

> sanitiseRegister :: Bool -> Register -> Word -> Word
> sanitiseRegister _ r v =
>     let val = if r == FaultIP || r == NextIP || r == FS_BASE || r == GS_BASE then
>                  if v > 0x00007fffffffffff && v < 0xffff800000000000 then 0 else v
>               else v
>     in
>         if r == FLAGS then
>             (val .|. sanitiseOrFlags) .&. sanitiseAndFlags
>         else val

> getSanitiseRegisterInfo :: PPtr TCB -> Kernel Bool
> getSanitiseRegisterInfo _ = return False

Here, cur = ksCurThread

> postModifyRegisters :: PPtr TCB -> PPtr TCB -> UserMonad ()
> postModifyRegisters cur dest =
>     when (dest /= cur) $ setRegister (RegisterSet.Register ErrorRegister) 0

> postSetFlags :: PPtr TCB -> TcbFlags -> Kernel ()
> postSetFlags t flags =
>     when (isFlagSet FpuDisabled flags) (fpuRelease t)
