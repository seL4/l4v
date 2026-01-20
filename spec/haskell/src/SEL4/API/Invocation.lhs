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
>         | InvokeReply (PPtr TCB) (PPtr CTE) Bool
>         | InvokeDomain DomainInvocation
>         | InvokeTCB TCBInvocation
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
>         | ThreadControl {
>             tcThread :: PPtr TCB,
>             tcThreadCapSlot :: PPtr CTE,
>             tcNewFaultEP :: Maybe CPtr,
>             tcNewMCPriority :: Maybe (Priority, PPtr TCB),
>             tcNewPriority :: Maybe (Priority, PPtr TCB),
>             tcNewCRoot, tcNewVRoot :: Maybe (Capability, PPtr CTE),
>             tcNewIPCBuffer :: Maybe (VPtr, Maybe (Capability, PPtr CTE)) }
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
>         | SetFlags {
>             setFlagsTCB :: PPtr TCB,
>             setFlagsClear :: Word,
>             setFlagsSet :: Word }
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
>         | SaveCaller {
>             targetSlot :: PPtr CTE }
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

\subsubsection{Domain Invocations}

The following data type defines the set of possible Domain invocation operations.

> data DomainInvocation
>         = InvokeDomainSet {
>             domThread :: PPtr TCB,
>             domDomain :: Domain }
>         | InvokeDomainScheduleSetStart {
>             domIndex :: Int }
>         | InvokeDomainScheduleConfigure {
>             domIndex :: Int,
>             domDomain :: Domain,
>             domDuration :: DomainDuration }
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

