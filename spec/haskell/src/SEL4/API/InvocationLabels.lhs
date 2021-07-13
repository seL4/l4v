%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the machine-independent invocation labels.

\begin{impdetails}

This module makes use of the GHC extension allowing data types with no constructors.

> {-# LANGUAGE EmptyDataDecls, CPP #-}

\end{impdetails}

> module SEL4.API.InvocationLabels where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine
> import qualified SEL4.API.InvocationLabels.TARGET as ArchLabels

\end{impdetails}

\subsection{Invocation Labels}

The following type enumerates all the kinds of invocations that clients can request of the kernel. The derived Enum instance defines the message label that clients should use when requesting that service. These labels are enumerated globally to ensure that no objects share an invocation label. This is to avoid confusion: service requests to the wrong object will fail immediately rather than perform unexpected actions.

> data GenInvocationLabels
>          = InvalidInvocation
>          | UntypedRetype
>          | TCBReadRegisters
>          | TCBWriteRegisters
>          | TCBCopyRegisters
>          | TCBConfigure
>          | TCBSetPriority
>          | TCBSetMCPriority
>          | TCBSetSchedParams
>          | TCBSetTimeoutEndpoint
>          | TCBSetIPCBuffer
>          | TCBSetSpace
>          | TCBSuspend
>          | TCBResume
>          | TCBBindNotification
>          | TCBUnbindNotification
>          | TCBSetTLSBase
>          | CNodeRevoke
>          | CNodeDelete
>          | CNodeCancelBadgedSends
>          | CNodeCopy
>          | CNodeMint
>          | CNodeMove
>          | CNodeMutate
>          | CNodeRotate
>          | IRQIssueIRQHandler
>          | IRQAckIRQ
>          | IRQSetIRQHandler
>          | IRQClearIRQHandler
>          | DomainSetSet
>          | SchedControlConfigureFlags
>          | SchedContextConsumed
>          | SchedContextBind
>          | SchedContextUnbind
>          | SchedContextUnbindObject
>          | SchedContextYieldTo
>         deriving (Show, Eq, Enum, Bounded)

> data InvocationLabel
>         = GenInvocationLabel GenInvocationLabels
>         | ArchInvocationLabel ArchLabels.ArchInvocationLabel
>         deriving (Show, Eq)

> instance Bounded InvocationLabel where
>     minBound = GenInvocationLabel InvalidInvocation
>     maxBound = ArchInvocationLabel $ (maxBound :: ArchLabels.ArchInvocationLabel)


> instance Enum InvocationLabel where
>     fromEnum e = case e of
>         GenInvocationLabel a -> fromEnum a
>         ArchInvocationLabel a -> apiMax + 1 + fromEnum a
>         where apiMax = fromEnum (maxBound :: GenInvocationLabels)
>     toEnum n =
>         if n <= apiMax then toEnum n
>         else ArchInvocationLabel $ toEnum (n - 1 - apiMax)
>         where apiMax = fromEnum (maxBound :: GenInvocationLabels)

Decode the invocation type requested by a particular message label.

> invocationType :: Word -> InvocationLabel
> invocationType x
>     | x' <= fromEnum (maxBound :: InvocationLabel) = toEnum x'
>     | otherwise = GenInvocationLabel InvalidInvocation
>     where x' = fromIntegral x

> genInvocationType :: Word -> GenInvocationLabels
> genInvocationType x =
>     case invocationType x of
>         GenInvocationLabel l -> l
>         ArchInvocationLabel _ -> InvalidInvocation

