%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

\begin{impdetails}

> {-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

\end{impdetails}

This module contains ARM-specific TCB management functions. Specifically, these functions are used by the "CopyRegisters" operation to transfer ARM-specific subsets of the register set.

There are presently no ARM-specific register subsets defined, but in future this may be extended to transfer floating point registers and other coprocessor state.

> module SEL4.Object.TCB.ARM_HYP where

\begin{impdetails}

> import SEL4.Machine(PPtr)
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.API.Failures
> import SEL4.API.Invocation.ARM_HYP
> import SEL4.Machine.RegisterSet.ARM_HYP
> import Data.Bits

> import Data.Word(Word8)

\end{impdetails}

> decodeTransfer :: Word8 -> KernelF SyscallError CopyRegisterSets
> decodeTransfer _ = return ARMNoExtraRegisters

> performTransfer :: CopyRegisterSets -> PPtr TCB -> PPtr TCB -> Kernel ()
> performTransfer _ _ _ = return ()

> sanitiseRegister :: TCB -> Register -> Word -> Word
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
> sanitiseRegister _ CPSR v = (v .&. 0xf8000000) .|. 0x150
#else
> sanitiseRegister tcb CPSR v =
>   if (atcbVCPUPtr (tcbArch tcb) /= Nothing && ((v .&. 0x1f) `elem` modes))
>       then v
>       else v'
>   where v' = (v .&. 0xf8000000) .|. 0x150
>         -- PMODE_(USER/FIQ/IRQ/SUPERVISOR/ABORT/UNDEFINED/SYSTEM)
>         modes = [0x10, 0x11, 0x12, 0x13, 0x17, 0x1b, 0x1f]
#endif
> sanitiseRegister _ _ v = v

