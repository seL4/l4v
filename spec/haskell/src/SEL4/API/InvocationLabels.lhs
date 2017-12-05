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
>         | SchedContextBind
>         | SchedContextUnbind
>         | SchedContextUnbindObject
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
>          TCBSetSpace -> 10
>          TCBSuspend -> 11
>          TCBResume -> 12
>          TCBBindNotification -> 13
>          TCBUnbindNotification -> 14
>          TCBSetTLSBase -> 15
>          CNodeRevoke -> 16
>          CNodeDelete -> 17
>          CNodeCancelBadgedSends -> 18
>          CNodeCopy -> 19
>          CNodeMint -> 20
>          CNodeMove -> 21
>          CNodeMutate -> 22
>          CNodeRotate -> 23
>          IRQIssueIRQHandler -> 24
>          IRQAckIRQ -> 25
>          IRQSetIRQHandler -> 26
>          IRQClearIRQHandler -> 27
>          TCBSetSchedContext -> 28
>          SchedControlConfigure -> 29
>          SchedContextBind -> 30
>          SchedContextUnbind -> 31
>          SchedContextUnbindObject -> 32
>          DomainSetSet -> apiMax
>          ArchInvocationLabel a -> apiMax + 1 + fromEnum a
>          where apiMax = 33
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
>         | n == 10 = TCBSetSpace
>         | n == 11 = TCBSuspend
>         | n == 12 = TCBResume
>         | n == 13 = TCBBindNotification
>         | n == 14 = TCBUnbindNotification
>         | n == 15 = TCBSetTLSBase
>         | n == 16 = CNodeRevoke
>         | n == 17 = CNodeDelete
>         | n == 18 = CNodeCancelBadgedSends
>         | n == 19 = CNodeCopy
>         | n == 20 = CNodeMint
>         | n == 21 = CNodeMove
>         | n == 22 = CNodeMutate
>         | n == 23 = CNodeRotate
>         | n == 24 = IRQIssueIRQHandler
>         | n == 25 = IRQAckIRQ
>         | n == 26 = IRQSetIRQHandler
>         | n == 27 = IRQClearIRQHandler
>         | n == 28 = TCBSetSchedContext
>         | n == 29 = SchedControlConfigure
>         | n == 30 = SchedContextBind
>         | n == 31 = SchedContextUnbind
>         | n == 32 = SchedContextUnbindObject
>         | n == 33 = DomainSetSet
>         | n > apiMax = ArchInvocationLabel $ toEnum (n - 1 - apiMax)
>         | otherwise = error "toEnum out of range for InvocationLabel"
>         where apiMax = 33

Decode the invocation type requested by a particular message label.

> invocationType :: Word -> InvocationLabel
> invocationType x
>     | x' <= fromEnum (maxBound :: InvocationLabel) = toEnum x'
>     | otherwise = InvalidInvocation
>     where x' = fromIntegral x

