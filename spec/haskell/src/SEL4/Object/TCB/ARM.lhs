%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

\begin{impdetails}

> {-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

\end{impdetails}

This module contains ARM-specific TCB management functions. Specifically, these functions are used by the "CopyRegisters" operation to transfer ARM-specific subsets of the register set.

There are presently no ARM-specific register subsets defined, but in future this may be extended to transfer floating point registers and other coprocessor state.

> module SEL4.Object.TCB.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine(PPtr)
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.Instances()
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Invocation.ARM
> import SEL4.Machine.RegisterSet(setRegister, UserMonad, VPtr(..))
> import qualified SEL4.Machine.RegisterSet as RegisterSet(Register(..))
> import SEL4.Machine.RegisterSet.ARM(Register(CPSR, TPIDRURW), Word)
> import Data.Bits
> import Data.Word(Word8)
> import Data.Maybe

\end{impdetails}

> decodeTransfer :: Word8 -> KernelF SyscallError CopyRegisterSets
> decodeTransfer _ = return ARMNoExtraRegisters

> performTransfer :: CopyRegisterSets -> PPtr TCB -> PPtr TCB -> Kernel ()
> performTransfer _ _ _ = return ()

> sanitiseRegister :: Bool -> Register -> Word -> Word
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
> sanitiseRegister _ CPSR v = (v .&. 0xf8000000) .|. 0x150
#else
> sanitiseRegister b CPSR v =
>   if (b && ((v .&. 0x1f) `elem` modes))
>       then v
>       else v'
>   where v' = (v .&. 0xf8000000) .|. 0x150
>         -- PMODE_(USER/FIQ/IRQ/SUPERVISOR/ABORT/UNDEFINED/SYSTEM)
>         modes = [0x10, 0x11, 0x12, 0x13, 0x17, 0x1b, 0x1f]
#endif
> sanitiseRegister _ _ v = v

> getSanitiseRegisterInfo :: PPtr TCB -> Kernel Bool
#ifndef CONFIG_ARM_HYPERVISOR_SUPPORT
> getSanitiseRegisterInfo _ = return False
#else
> getSanitiseRegisterInfo t = do
>    v <- liftM (atcbVCPUPtr . tcbArch) $ getObject t
>    return $ isJust v
#endif

> postModifyRegisters :: PPtr TCB -> PPtr TCB -> UserMonad ()
> postModifyRegisters cur ptr = return ()

> postSetFlags :: PPtr TCB -> TcbFlags -> Kernel ()
> postSetFlags t flags = return ()

> prepareSetDomain :: PPtr TCB -> Domain -> Kernel ()
> prepareSetDomain t newDom = return ()
