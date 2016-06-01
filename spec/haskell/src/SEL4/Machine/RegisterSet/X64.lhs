% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines the x86 64-bit register set.

> module SEL4.Machine.RegisterSet.X64 where

\begin{impdetails}

> import qualified Data.Word
> import Data.Array
> import Data.Bits

\end{impdetails}

> data Register =
>     RAX | RBX | RCX | RDX | RSI | RDI | RBP |
>     R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15 | DS | ES | FS | GS |
>     FaultInstruction | -- "FaultIP"
>     TLS_BASE | PADDING_REGISTER |
>     ErrorRegister | NextIP | CS | RFLAGS | RSP | SS
>     deriving (Eq, Enum, Bounded, Ord, Ix, Show)

> type Word = Data.Word.Word64

> capRegister = RBX
> msgInfoRegister = RSI
> msgRegisters = [RDI, RBP]
> badgeRegister = capRegister
> frameRegisters = FaultInstruction : RSP : RFLAGS : [RAX .. R15]
> gpRegisters = [TLS_BASE, FS, GS]
> exceptionMessage = [FaultInstruction, RSP, RFLAGS]

> syscallMessage = [RAX .. RBP] ++ [NextIP, RSP, RFLAGS]

> data GDTSlot
>     = GDT_NULL
>     | GDT_CS_0
>     | GDT_DS_0
>     | GDT_TSS
>     | GDT_TSS_Padding
>     | GDT_CS_3
>     | GDT_DS_3
>     | GDT_TLS
>     | GDT_IPCBUF
>     | GDT_ENTRIES
>     deriving (Eq, Show, Enum, Ord, Ix)

> gdtToSel :: GDTSlot -> Word
> gdtToSel g = (fromIntegral (fromEnum g) `shiftL` 3 ) .|. 3

> gdtToSel_masked :: GDTSlot -> Word
> gdtToSel_masked g = gdtToSel g .|. 3

> selCS3 = gdtToSel_masked GDT_CS_3
> selDS3 = gdtToSel_masked GDT_DS_3
> selTLS = gdtToSel_masked GDT_TLS
> selIPCBUF = gdtToSel_masked GDT_IPCBUF
> selCS0 = gdtToSel_masked GDT_CS_0
> selDS0 = gdtToSel GDT_DS_0

> initContext :: [(Register, Word)]
> initContext = [(DS, selDS3), (ES, selDS3), (CS, selCS3), (SS, selDS3)
>               ,(RFLAGS, bit 9 .|. bit 1)] -- User mode

%FIXME x64: add FPU context

> sanitiseRegister :: Register -> Word -> Word
> sanitiseRegister RFLAGS v =
>     v .|. bit 1 .&. (complement (bit 3)) .&. (complement (bit 5))  .|. bit 9
>     .&. (bit 12 - 1)
> sanitiseRegister FS v = if v /= selTLS && v /= selIPCBUF then 0 else v
> sanitiseRegister GS v = if v /= selTLS && v /= selIPCBUF then 0 else v
> sanitiseRegister _ v = v

