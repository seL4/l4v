%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the interfaces presented to clients by the kernel's objects.

\begin{impdetails}

We use the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.API.Invocation where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.API.Types
> import SEL4.Object.Structures

\end{impdetails}

The architecture-specific definitions are imported qualified with the "Arch" prefix.

> import qualified SEL4.API.Invocation.TARGET as Arch

\subsection{Invocation Type}

The following type can specify any kernel object invocation. It contains physical pointers to any kernel objects required for the operation, and other arguments decoded from the message registers.

> data Invocation
>         = InvokeUntyped UntypedInvocation
>         | InvokeEndpoint (PPtr Endpoint) Word Bool Bool
>         | InvokeNotification (PPtr Notification) Word
>         | InvokeReply (PPtr Reply) Bool
>         | InvokeDomain (PPtr TCB) Domain
>         | InvokeTCB TCBInvocation
>         | InvokeSchedContext SchedContextInvocation
>         | InvokeSchedControl SchedControlInvocation
>         | InvokeCNode CNodeInvocation
>         | InvokeIRQControl IRQControlInvocation
>         | InvokeIRQHandler IRQHandlerInvocation
>         | InvokeArchObject Arch.Invocation
>         deriving Show

\subsubsection{TCB Object Invocations}

The following data type defines the set of possible TCB invocation operations. The operations are discussed and defined in more detail in \autoref{sec:object.tcb}.

> data TCBInvocation
>         = Suspend { suspendThread :: PPtr TCB }
>         | Resume { resumeThread :: PPtr TCB }
>         | ThreadControlCaps {
>             tcCapsTarget :: PPtr TCB,
>             tcCapsSlot :: PPtr CTE,
>             tcCapsFaultHandler :: Maybe (Capability, PPtr CTE),
>             tcCapsTimeoutHandler :: Maybe (Capability, PPtr CTE),
>             tcCapsCRoot :: Maybe (Capability, PPtr CTE),
>             tcCapsVRoot :: Maybe (Capability, PPtr CTE),
>             tcCapsBuffer :: Maybe (VPtr, Maybe (Capability, PPtr CTE)) }
>         | ThreadControlSched {
>             tcSchedTarget :: PPtr TCB,
>             tcSchedSlot :: PPtr CTE,
>             tcSchedFaultHandler :: Maybe (Capability, PPtr CTE),
>             tcSchedMCPriority :: Maybe (Priority, PPtr TCB),
>             tcSchedPriority :: Maybe (Priority, PPtr TCB),
>             tcSchedSchedContext :: Maybe (Maybe (PPtr SchedContext)) }
>         | NotificationControl {
>             notificationTCB :: PPtr TCB,
>             notificationPtr :: Maybe (PPtr Notification) }
>         | WriteRegisters {
>             writeRegsThread :: PPtr TCB,
>             writeRegsResume :: Bool,
>             writeRegsValues :: [Word],
>             writeRegsArch :: Arch.CopyRegisterSets }
>         | ReadRegisters {
>             readRegsThread :: PPtr TCB,
>             readRegsSuspend :: Bool,
>             readRegsLength :: Word,
>             readRegsArch :: Arch.CopyRegisterSets }
>         | CopyRegisters {
>             copyRegsTarget :: PPtr TCB,
>             copyRegsSource :: PPtr TCB,
>             copyRegsSuspendSource, copyRegsResumeTarget :: Bool,
>             copyRegsTransferFrame, copyRegsTransferInteger :: Bool,
>             copyRegsTransferArch :: Arch.CopyRegisterSets }
>         | SetTLSBase {
>             setTLSBaseTCB :: PPtr TCB,
>             setTLSBaseNewBase :: Word }
>         deriving Show

> data SchedContextInvocation
>         = InvokeSchedContextConsumed {
>             consumedScPtr :: PPtr SchedContext,
>             consumedbuffer :: Maybe (PPtr Word) }
>         | InvokeSchedContextBind {
>             bindScPtr :: PPtr SchedContext,
>             bindCap :: Capability }
>         | InvokeSchedContextUnbindObject {
>             unbindObjectScPtr :: PPtr SchedContext,
>             unbindObjectCap :: Capability }
>         | InvokeSchedContextUnbind { unbindScPtr :: PPtr SchedContext }
>         | InvokeSchedContextYieldTo {
>             yieldToScPtr :: PPtr SchedContext,
>             yieldTobuffer :: Maybe (PPtr Word) }
>         deriving Show

> data SchedControlInvocation
>         = InvokeSchedControlConfigureFlags {
>             schedControlScPtr :: PPtr SchedContext,
>             schedControlBudget :: Ticks,
>             schedControlPeriod :: Ticks,
>             schedControlNRefills :: Int,
>             schedControlBadge :: Word,
>             schedControlFlags :: Word }
>         deriving Show

\subsubsection{CNode Invocations}

The following data type defines the set of possible CNode invocation operations. The operations are discussed and defined in more detail in \autoref{sec:object.cnode}.

> data CNodeInvocation
>         = Insert {
>             insertCap :: Capability,
>             sourceSlot, targetSlot :: PPtr CTE }
>         | Rotate {
>             moveCap1, moveCap2 :: Capability,
>             sourceSlot, pivotSlot, targetSlot :: PPtr CTE }
>         | Revoke { targetSlot :: PPtr CTE }
>         | Move {
>             moveCap :: Capability,
>             sourceSlot, targetSlot :: PPtr CTE }
>         | CancelBadgedSends { epCap :: Capability }
>         | Delete { targetSlot :: PPtr CTE }
>         deriving Show

\subsubsection{Untyped Invocations}

The following data type defines the parameters expected for invocations of Untyped objects.

> data UntypedInvocation
>         = Retype {
>             retypeSource :: PPtr CTE,
>             retypeResetUntyped :: Bool,
>             retypeRegionBase :: PPtr (),
>             retypeFreeRegionBase :: PPtr (),
>             retypeNewType :: ObjectType,
>             retypeNewSizeBits :: Int,
>             retypeSlots :: [PPtr CTE],
>             retypeIsDevice :: Bool }
>         deriving Show

\subsubsection{Interrupt Controller Invocations}

The following data type defines the set of possible invocations for interrupt controller capabilities.

%FIXME IssueIRQHandler is not really handled on x64, instead it has two arch-specific ones

> data IRQControlInvocation
>         = ArchIRQControl { archIRQControl :: Arch.IRQControlInvocation }
>         | IssueIRQHandler {
>             issueHandlerIRQ :: IRQ,
>             issueHandlerSlot,
>             issueHandlerControllerSlot :: PPtr CTE }
>         deriving Show

\subsubsection{IRQ Handler Invocations}

The following data type defines the set of possible invocations for IRQ capabilities.

> data IRQHandlerInvocation
>         = AckIRQ { irqHandlerIRQ :: IRQ }
>         | ClearIRQHandler { irqHandlerIRQ :: IRQ }
>         | SetIRQHandler {
>             irqHandlerIRQ :: IRQ,
>             setIRQHandlerCap :: Capability,
>             setIRQHandlerSlot :: PPtr CTE }
>         deriving Show

