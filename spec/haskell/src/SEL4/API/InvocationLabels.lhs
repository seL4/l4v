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
>         | CNodeSaveCaller
>         | IRQIssueIRQHandler
>         | IRQAckIRQ
>         | IRQSetIRQHandler
>         | IRQClearIRQHandler
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
>          CNodeSaveCaller -> 24
>          IRQIssueIRQHandler -> 25
>          IRQAckIRQ -> 26
>          IRQSetIRQHandler -> 27
>          IRQClearIRQHandler -> 28
>          DomainSetSet -> apiMax
>          ArchInvocationLabel a -> apiMax + 1 + fromEnum a
>          where apiMax = 29
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
>         | n == 24 = CNodeSaveCaller
>         | n == 25 = IRQIssueIRQHandler
>         | n == 26 = IRQAckIRQ
>         | n == 27 = IRQSetIRQHandler
>         | n == 28 = IRQClearIRQHandler
>         | n == 29 = DomainSetSet
>         | n > apiMax = ArchInvocationLabel $ toEnum (n - 1 - apiMax)
>         | otherwise = error "toEnum out of range for InvocationLabel"
>         where apiMax = 29

Decode the invocation type requested by a particular message label.

> invocationType :: Word -> InvocationLabel
> invocationType x
>     | x' <= fromEnum (maxBound :: InvocationLabel) = toEnum x'
>     | otherwise = InvalidInvocation
>     where x' = fromIntegral x

