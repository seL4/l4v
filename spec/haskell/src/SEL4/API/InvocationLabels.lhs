%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
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

> data InvocationLabel
>         = InvalidInvocation
>         | UntypedRetype
>         | TCBReadRegisters
>         | TCBWriteRegisters
>         | TCBCopyRegisters
>         | TCBConfigure
>         | TCBSetPriority
>         | TCBSetMCPriority
>         | TCBSetSchedParams
>         | TCBSetTimeoutEndpoint
>         | TCBSetIPCBuffer
>         | TCBSetSchedContext
>         | TCBSetSpace
>         | TCBSuspend
>         | TCBResume
>         | TCBBindNotification
>         | TCBUnbindNotification
>         | TCBSetTLSBase
>         | CNodeRevoke
>         | CNodeDelete
>         | CNodeCancelBadgedSends
>         | CNodeCopy
>         | CNodeMint
>         | CNodeMove
>         | CNodeMutate
>         | CNodeRotate
>         | IRQIssueIRQHandler
>         | IRQAckIRQ
>         | IRQSetIRQHandler
>         | IRQClearIRQHandler
>         | DomainSetSet
>         | SchedControlConfigure
>         | SchedContextConsumed
>         | SchedContextBind
>         | SchedContextUnbind
>         | SchedContextUnbindObject
>         | SchedContextYieldTo
>         | ArchInvocationLabel ArchLabels.ArchInvocationLabel
>         deriving (Show, Eq)

> instance Bounded InvocationLabel where
>     minBound = InvalidInvocation
>     maxBound = ArchInvocationLabel $ (maxBound :: ArchLabels.ArchInvocationLabel)

> instance Enum InvocationLabel where
>     fromEnum e = case e of
>          InvalidInvocation -> 0
>          UntypedRetype -> 1
>          TCBReadRegisters -> 2
>          TCBWriteRegisters -> 3
>          TCBCopyRegisters -> 4
>          TCBConfigure -> 5
>          TCBSetPriority -> 6
>          TCBSetMCPriority -> 7
>          TCBSetSchedParams -> 8
>          TCBSetTimeoutEndpoint -> 9
>          TCBSetIPCBuffer -> 10
>          TCBSetSpace -> 11
>          TCBSuspend -> 12
>          TCBResume -> 13
>          TCBBindNotification -> 14
>          TCBUnbindNotification -> 15
>          TCBSetTLSBase -> 16
>          CNodeRevoke -> 17
>          CNodeDelete -> 18
>          CNodeCancelBadgedSends -> 19
>          CNodeCopy -> 20
>          CNodeMint -> 21
>          CNodeMove -> 22
>          CNodeMutate -> 23
>          CNodeRotate -> 24
>          IRQIssueIRQHandler -> 25
>          IRQAckIRQ -> 26
>          IRQSetIRQHandler -> 27
>          IRQClearIRQHandler -> 28
>          TCBSetSchedContext -> 29
>          SchedControlConfigure -> 30
>          SchedContextConsumed -> 31
>          SchedContextBind -> 32
>          SchedContextUnbind -> 33
>          SchedContextUnbindObject -> 34
>          SchedContextYieldTo -> 35
>          DomainSetSet -> apiMax
>          ArchInvocationLabel a -> apiMax + 1 + fromEnum a
>          where apiMax = 36
>     toEnum n
>         | n == 0 = InvalidInvocation
>         | n == 1 = UntypedRetype
>         | n == 2 = TCBReadRegisters
>         | n == 3 = TCBWriteRegisters
>         | n == 4 = TCBCopyRegisters
>         | n == 5 = TCBConfigure
>         | n == 6 = TCBSetMCPriority
>         | n == 7 = TCBSetPriority
>         | n == 8 = TCBSetSchedParams
>         | n == 9 = TCBSetTimeoutEndpoint
>         | n == 10 = TCBSetIPCBuffer
>         | n == 11 = TCBSetSpace
>         | n == 12 = TCBSuspend
>         | n == 13 = TCBResume
>         | n == 14 = TCBBindNotification
>         | n == 15 = TCBUnbindNotification
>         | n == 16 = TCBSetTLSBase
>         | n == 17 = CNodeRevoke
>         | n == 18 = CNodeDelete
>         | n == 19 = CNodeCancelBadgedSends
>         | n == 20 = CNodeCopy
>         | n == 21 = CNodeMint
>         | n == 22 = CNodeMove
>         | n == 23 = CNodeMutate
>         | n == 24 = CNodeRotate
>         | n == 25 = IRQIssueIRQHandler
>         | n == 26 = IRQAckIRQ
>         | n == 27 = IRQSetIRQHandler
>         | n == 28 = IRQClearIRQHandler
>         | n == 29 = TCBSetSchedContext
>         | n == 30 = SchedControlConfigure
>         | n == 31 = SchedContextConsumed
>         | n == 32 = SchedContextBind
>         | n == 33 = SchedContextUnbind
>         | n == 34 = SchedContextUnbindObject
>         | n == 35 = SchedContextYieldTo
>         | n == 36 = DomainSetSet
>         | n > apiMax = ArchInvocationLabel $ toEnum (n - 1 - apiMax)
>         | otherwise = error "toEnum out of range for InvocationLabel"
>         where apiMax = 36

Decode the invocation type requested by a particular message label.

> invocationType :: Word -> InvocationLabel
> invocationType x
>     | x' <= fromEnum (maxBound :: InvocationLabel) = toEnum x'
>     | otherwise = InvalidInvocation
>     where x' = fromIntegral x

