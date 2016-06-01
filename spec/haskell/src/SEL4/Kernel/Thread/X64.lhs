% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module contains the architecture-specific thread switch code for X86-64bit.

> module SEL4.Kernel.Thread.X64 where

\begin{impdetails}

> import SEL4.Machine
> import qualified SEL4.Machine.RegisterSet.X64 as ArchReg
> import SEL4.Model.StateData
> import SEL4.Model.StateData.X64
> import SEL4.Object.Structures
> import SEL4.Object.TCB
> import SEL4.Kernel.VSpace.X64
> import qualified SEL4.Machine.Hardware.X64 as Arch
> import {-# SOURCE #-} SEL4.Kernel.Init
> import Data.Array
> import Data.Bits

\end{impdetails}


> -- Current C code doesn't work for addresses above 32 bits.
> -- This is meant to take a base address and craft a default
> -- gdt_data structure
> baseToGDTDataWord :: Word -> Word
> baseToGDTDataWord p = error "Unimplemented"

> switchToThread :: PPtr TCB -> Kernel ()
> switchToThread tcb = do
>     setVMRoot tcb
>     gdt <- gets $ x64KSGDT . ksArchState
>     base <- asUser tcb $ getRegister (Register ArchReg.TLS_BASE)
>     let gdt_tls_slot = fromIntegral (fromEnum ArchReg.GDT_TLS) `shiftL` gdteBits
>     doMachineOp $ storeWord (gdt + gdt_tls_slot) $ baseToGDTDataWord $ base
>     bufferPtr <- threadGet tcbIPCBuffer tcb
>     let gdt_ipcbuf_slot = fromIntegral (fromEnum ArchReg.GDT_IPCBUF) `shiftL` gdteBits
>     doMachineOp $ storeWord (gdt + gdt_ipcbuf_slot) $ baseToGDTDataWord $ fromVPtr bufferPtr

> configureIdleThread :: PPtr TCB -> KernelInit ()
> configureIdleThread _ = error "Unimplemented. init code"

> switchToIdleThread :: Kernel ()
> switchToIdleThread = return ()

> activateIdleThread :: PPtr TCB -> Kernel ()
> activateIdleThread _ = return ()

