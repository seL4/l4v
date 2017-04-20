% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines IO port routines, specific to x64.

> module SEL4.Object.IOPort.X64 where

\begin{impdetails}

> {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures SEL4.Object.Instances() SEL4.API.Failures SEL4.API.Invocation.X64%ArchInv #-}
> {-# BOOT-EXPORTS: performX64PortInvocation decodeX64PortInvocation #-}

> import SEL4.Machine
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.Machine.Hardware.X64
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.TCB
> import SEL4.API.Invocation.X64 as ArchInv
> import SEL4.API.InvocationLabels
> import SEL4.API.InvocationLabels.X64

\end{impdetails}

> ensurePortOperationAllowed :: ArchCapability -> IOPort -> Int ->
>     KernelF SyscallError ()
> ensurePortOperationAllowed (IOPortCap { capIOPortFirstPort = first_allowed, capIOPortLastPort = last_allowed }) start_port size = do
>     let end_port = start_port + fromIntegral size - 1
>     assert (first_allowed <= last_allowed) "first allowed must be less than last allowed"
>     when (start_port > end_port) $ throw IllegalOperation
>     when ((start_port < first_allowed) || (end_port > last_allowed)) $
>         throw IllegalOperation
> ensurePortOperationAllowed _ _ _ = fail "Unreachable"

%FIXME port+output data packing in C, see SELFOUR-360

%FIXME downcast to 16-bit port from 64-bit arg happens before range check, which
%      is likely incorrect

> decodeX64PortInvocation :: Word -> [Word] ->
>         ArchCapability -> KernelF SyscallError ArchInv.Invocation
> decodeX64PortInvocation label args cap@(IOPortCap {})  = do
>     case (invocationType label, args) of
>         (ArchInvocationLabel X64IOPortIn8, port':_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap port 1
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortIn8
>         (ArchInvocationLabel X64IOPortIn8, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortIn16, port':_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap port 2
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortIn16
>         (ArchInvocationLabel X64IOPortIn16, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortIn32, port':_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap port 4
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortIn32
>         (ArchInvocationLabel X64IOPortIn32, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortOut8, port':out:_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap port 1
>             let output_data = fromIntegral out
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortOut8 output_data
>         (ArchInvocationLabel X64IOPortOut8, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortOut16, port':out:_)-> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap port 2
>             let output_data = fromIntegral out
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortOut16 output_data
>         (ArchInvocationLabel X64IOPortOut16, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortOut32, port':out:_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap port 4
>             let output_data = fromIntegral out
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortOut32 output_data
>         (ArchInvocationLabel X64IOPortOut32, _) -> throw TruncatedMessage
>         (_, _) -> throw IllegalOperation
> decodeX64PortInvocation _ _ _ = fail "Unreachable"

> portIn f = do
>       ct <- getCurThread
>       res <- doMachineOp $ f
>       setMRs ct Nothing [res]
>       msgInfo <- return $ MI {
>           msgLength = 1,
>           msgExtraCaps = 0,
>           msgCapsUnwrapped = 0,
>           msgLabel = 0 }
>       setMessageInfo ct msgInfo

> portOut f w = do
>        ct <- getCurThread
>        doMachineOp $ f w
>        setMessageInfo ct $ MI 0 0 0 0


>
> performX64PortInvocation :: ArchInv.Invocation -> KernelP [Word]
> performX64PortInvocation (InvokeIOPort (IOPortInvocation port port_data)) = withoutPreemption $ do
>     case port_data of
>         ArchInv.IOPortIn8 -> portIn $ in8 port
>         ArchInv.IOPortIn16 -> portIn $ in16 port
>         ArchInv.IOPortIn32 -> portIn $ in32 port
>         ArchInv.IOPortOut8 w -> portOut (out8 port) w
>         ArchInv.IOPortOut16 w -> portOut (out16 port) w
>         ArchInv.IOPortOut32 w -> portOut (out32 port) w
>     return $ []

> performX64PortInvocation _ = fail "Unreachable"

