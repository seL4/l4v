%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines IO port routines, specific to x64.

> module SEL4.Object.IOPort.X64 where

\begin{impdetails}

> {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures SEL4.Object.Instances() SEL4.API.Failures SEL4.API.Invocation.X64%ArchInv #-}
> {-# BOOT-EXPORTS: performX64PortInvocation decodeX64PortInvocation #-}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.Machine.Hardware.X64
> import SEL4.Model
> import SEL4.Model.StateData.X64 hiding (KernelState)
> import SEL4.Object.Structures
> import SEL4.Object.TCB
> import SEL4.Object.ObjectType.X64
> import SEL4.API.Invocation.X64 as ArchInv
> import SEL4.API.InvocationLabels
> import SEL4.API.InvocationLabels.X64
> import SEL4.Object.CNode
> import SEL4.Kernel.CSpace

> import Data.Bool
> import Data.Array
> import Data.Word(Word32)

\end{impdetails}

> ensurePortOperationAllowed :: ArchCapability -> Word32 -> Int ->
>     KernelF SyscallError ()
> ensurePortOperationAllowed (IOPortCap { capIOPortFirstPort = first_allowed, capIOPortLastPort = last_allowed }) start_port size = do
>     let end_port = start_port + fromIntegral size - 1
>     assert (first_allowed <= last_allowed) "first allowed must be less than last allowed"
>     assert (start_port <= end_port) "first requested must be less than last requested"
>     when ((start_port < fromIntegral first_allowed) || (end_port > fromIntegral last_allowed)) $
>         throw IllegalOperation
> ensurePortOperationAllowed _ _ _ = fail "Unreachable"

> isIOPortRangeFree :: IOPort -> IOPort -> Kernel Bool
> isIOPortRangeFree f l = do
>     ports <- gets (x64KSAllocatedIOPorts . ksArchState)
>     return $ not $ foldl (\x y -> x || ports ! y) False [f..l]

%FIXME port+output data packing in C, see SELFOUR-360

%FIXME downcast to 16-bit port from 64-bit arg happens before range check, which
%      is likely incorrect

> decodeX64PortInvocation :: Word -> [Word] -> PPtr CTE ->
>         ArchCapability -> [Capability] -> KernelF SyscallError ArchInv.Invocation
> decodeX64PortInvocation label args _ cap@(IOPortCap {}) _  = do
>     case (invocationType label, args) of
>         (ArchInvocationLabel X64IOPortIn8, port':_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap (fromIntegral port) 1
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortIn8
>         (ArchInvocationLabel X64IOPortIn8, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortIn16, port':_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap (fromIntegral port) 2
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortIn16
>         (ArchInvocationLabel X64IOPortIn16, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortIn32, port':_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap (fromIntegral port) 4
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortIn32
>         (ArchInvocationLabel X64IOPortIn32, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortOut8, port':out:_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap (fromIntegral port) 1
>             let output_data = fromIntegral out
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortOut8 output_data
>         (ArchInvocationLabel X64IOPortOut8, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortOut16, port':out:_)-> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap (fromIntegral port) 2
>             let output_data = fromIntegral out
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortOut16 output_data
>         (ArchInvocationLabel X64IOPortOut16, _) -> throw TruncatedMessage
>         (ArchInvocationLabel X64IOPortOut32, port':out:_) -> do
>             let port = (fromIntegral port') :: IOPort
>             ensurePortOperationAllowed cap (fromIntegral port) 4
>             let output_data = fromIntegral out
>             return $ InvokeIOPort $ IOPortInvocation port $ IOPortOut32 output_data
>         (ArchInvocationLabel X64IOPortOut32, _) -> throw TruncatedMessage
>         (_, _) -> throw IllegalOperation

> decodeX64PortInvocation label args slot IOPortControlCap extraCaps = do
>     case (invocationType label, args, extraCaps) of
>         (ArchInvocationLabel X64IOPortControlIssue, f:l:index:depth:_, cnode:_) -> do
>             let firstPort = (fromIntegral f) :: IOPort
>             let lastPort = (fromIntegral l) :: IOPort
>
>             when (firstPort > lastPort) $ throw $ InvalidArgument 1
>             check <- withoutFailure $ isIOPortRangeFree firstPort lastPort
>             unless check $ throw RevokeFirst
>
>             destSlot <- lookupTargetSlot cnode (CPtr index) (fromIntegral depth)
>             ensureEmptySlot destSlot
>             return $ InvokeIOPortControl $ IOPortControlIssue firstPort lastPort destSlot slot
>         (ArchInvocationLabel X64IOPortControlIssue, _, _) -> throw TruncatedMessage
>         _ -> throw IllegalOperation

> decodeX64PortInvocation _ _ _ _ _ = fail "Unreachable"

> portIn f = do
>       res <- doMachineOp $ f
>       return [res]

> portOut f w = do
>        doMachineOp $ f w
>        return []

We do not need all of IO port validity in the refinement proof, but do need to
cross over the constraint that all IO port caps in the state have been issued.

> allIOPortsIssued_asrt :: KernelState -> Bool
> allIOPortsIssued_asrt _ = True

> performX64PortInvocation :: ArchInv.Invocation -> KernelP [Word]
> performX64PortInvocation (InvokeIOPort (IOPortInvocation port port_data)) = withoutPreemption $
>     case port_data of
>         ArchInv.IOPortIn8 -> portIn $ in8 port
>         ArchInv.IOPortIn16 -> portIn $ in16 port
>         ArchInv.IOPortIn32 -> portIn $ in32 port
>         ArchInv.IOPortOut8 w -> portOut (out8 port) w
>         ArchInv.IOPortOut16 w -> portOut (out16 port) w
>         ArchInv.IOPortOut32 w -> portOut (out32 port) w

> performX64PortInvocation (InvokeIOPortControl (IOPortControlIssue f l destSlot srcSlot)) =
>   withoutPreemption $ do
>     stateAssert allIOPortsIssued_asrt "all_io_ports_issued'"
>     setIOPortMask f l True
>     cteInsert (ArchObjectCap (IOPortCap f l)) srcSlot destSlot
>     return []

> performX64PortInvocation _ = fail "Unreachable"

