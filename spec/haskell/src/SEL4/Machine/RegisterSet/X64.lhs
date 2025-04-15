%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

> {-# LANGUAGE FlexibleContexts #-}

This module defines the x86 64-bit register set.

> module SEL4.Machine.RegisterSet.X64 where

\begin{impdetails}

> import Prelude hiding (Word)
> import qualified Data.Word
> import Data.Array
> import Data.Bits
> import Data.Helpers

> import Control.Monad.State(State, gets, modify)

\end{impdetails}

> data Register =
>     RAX | RBX | RCX | RDX | RSI | RDI | RBP |
>     R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 |
>     FaultIP | -- "FaultIP"
>     FS_BASE | GS_BASE |
>     ErrorRegister | NextIP | CS | FLAGS | RSP | SS
>     deriving (Eq, Enum, Bounded, Ord, Ix, Show)

> type Word = Data.Word.Word64

> capRegister = RDI
> msgInfoRegister = RSI
> msgRegisters = [R10, R8, R9, R15]
> badgeRegister = capRegister
> faultRegister = FaultIP
> nextInstructionRegister = NextIP
> frameRegisters = FaultIP : RSP : FLAGS : [RAX .. R15]
> gpRegisters = [FS_BASE, GS_BASE]
> exceptionMessage = [FaultIP, RSP, FLAGS]
> tlsBaseRegister = FS_BASE

> syscallMessage = [RAX .. R15] ++ [FaultIP, RSP, FLAGS]

> data GDTSlot
>     = GDT_NULL
>     | GDT_CS_0
>     | GDT_DS_0
>     | GDT_TSS
>     | GDT_TSS_Padding
>     | GDT_CS_3
>     | GDT_DS_3
>     | GDT_FS
>     | GDT_GS
>     | GDT_ENTRIES
>     deriving (Eq, Show, Enum, Ord, Ix)

> gdtToSel :: GDTSlot -> Word
> gdtToSel g = (fromIntegral (fromEnum g) `shiftL` 3 ) .|. 3

> gdtToSel_masked :: GDTSlot -> Word
> gdtToSel_masked g = gdtToSel g .|. 3

> selCS3 = gdtToSel_masked GDT_CS_3
> selDS3 = gdtToSel_masked GDT_DS_3
> selFS = gdtToSel_masked GDT_FS
> selGS = gdtToSel_masked GDT_GS
> selCS0 = gdtToSel_masked GDT_CS_0
> selDS0 = gdtToSel GDT_DS_0

> initContext :: [(Register, Word)]
> initContext = [ (CS, selCS3)
>               , (SS, selDS3)
>               , (FLAGS, bit 9 .|. bit 1) -- User mode
>               ]

\subsubsection{User-level Context}

On X64 the representation of the user-level context of a thread is an array
of machine words, indexed by register name for the user registers, plus the
state of the FPU, which we represent as a function from machine word to bytes
with the convention that all unused entries map to 0.

> type FPUState = Array Word Data.Word.Word8

> data UserContext = UC { fromUC :: Array Register Word,
>                         userFpuState :: FPUState }
>   deriving Show


A new user-level context is a list of values for the machine's registers.
Registers are generally initialised to 0, but there may be machine-specific
initial values for certain registers. The FPU state contains 576 bytes,
initialised to 0.

> newContext :: UserContext
> newContext = UC ((funArray $ const 0)//initContext) (funPartialArray (const 0) (0,575))

Functions are provided to get and set a single register, or to get and set the FPU state.

> getRegister r = gets $ (! r) . fromUC

> setRegister r v = modify (\ uc -> UC (fromUC uc //[(r, v)]) (userFpuState uc))

> getFPUState :: State UserContext FPUState
> getFPUState = gets userFpuState

> setFPUState fc = modify (\ uc -> UC (fromUC uc) fc)
