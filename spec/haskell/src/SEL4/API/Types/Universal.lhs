%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the set of kernel object types that are available on all implementations.

> module SEL4.API.Types.Universal where

> import Data.WordLib

\subsection{Types}

\subsubsection{Object Types}

The following is the definition of the seven object types that are always available, as well as untyped memory. This enumeration may be extended on some platforms to add platform-specific object types.

> data APIObjectType
>         = Untyped
>         | TCBObject
>         | EndpointObject
>         | NotificationObject
>         | CapTableObject
>         | SchedContextObject
>         | ReplyObject
>         deriving (Enum, Bounded, Eq, Show)

> epSizeBits :: Int
> epSizeBits = 4

> ntfnSizeBits :: Int
> ntfnSizeBits = wordSizeCase 5 5

> cteSizeBits :: Int
> cteSizeBits = wordSizeCase 4 5

> replySizeBits :: Int
> replySizeBits = wordSizeCase 4 5

> minSchedContextBits :: Int
> minSchedContextBits = 8

> schedContextSporadicFlag :: Int
> schedContextSporadicFlag = 1
