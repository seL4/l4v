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
>         | TCBSetIPCBuffer
>         | TCBSetTimeoutEndpoint
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
>         | SchedControlConfigure
>         | SchedContextConsumed
>         | SchedContextBind
>         | SchedContextUnbind
>         | SchedContextUnbindObject
>         | SchedContextYieldTo
>         | DomainSetSet
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
>          TCBSetIPCBuffer -> 9
>          TCBSetTimeoutEndpoint -> 10
>          TCBSetSchedContext -> 11
>          TCBSetSpace -> 12
>          TCBSuspend -> 13
>          TCBResume -> 14
>          TCBBindNotification -> 15
>          TCBUnbindNotification -> 16
>          TCBSetTLSBase -> 17
>          CNodeRevoke -> 18
>          CNodeDelete -> 19
>          CNodeCancelBadgedSends -> 20
>          CNodeCopy -> 21
>          CNodeMint -> 22
>          CNodeMove -> 23
>          CNodeMutate -> 24
>          CNodeRotate -> 25
>          IRQIssueIRQHandler -> 26
>          IRQAckIRQ -> 27
>          IRQSetIRQHandler -> 28
>          IRQClearIRQHandler -> 29
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
>         | n == 9 = TCBSetIPCBuffer
>         | n == 10 = TCBSetTimeoutEndpoint
>         | n == 11 = TCBSetSchedContext
>         | n == 12 = TCBSetSpace
>         | n == 13 = TCBSuspend
>         | n == 14 = TCBResume
>         | n == 15 = TCBBindNotification
>         | n == 16 = TCBUnbindNotification
>         | n == 17 = TCBSetTLSBase
>         | n == 18 = CNodeRevoke
>         | n == 18 = CNodeDelete
>         | n == 20 = CNodeCancelBadgedSends
>         | n == 21 = CNodeCopy
>         | n == 22 = CNodeMint
>         | n == 23 = CNodeMove
>         | n == 24 = CNodeMutate
>         | n == 25 = CNodeRotate
>         | n == 26 = IRQIssueIRQHandler
>         | n == 27 = IRQAckIRQ
>         | n == 28 = IRQSetIRQHandler
>         | n == 28 = IRQClearIRQHandler
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

