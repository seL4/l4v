%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the machine-specific invocations for x86 64bit.

\begin{impdetails}

This module makes use of the GHC extension allowing data types with no constructors.

> {-# LANGUAGE EmptyDataDecls #-}

\end{impdetails}

> module SEL4.API.InvocationLabels.X64 where

\subsection{x86-64-Specific Invocation Labels}

%FIXME still in flux, some invcations may be 32-bit only (to be removed).

%FIXME the XML says PML4s can be invoked; they can't.
%Note: there is no unmap for IO pages.

%FIXME: other things that don't exist: IOSpaceRemovePassthrough, IOSpaceUnmap

> data ArchInvocationLabel
>         = X64PDPTMap
>         | X64PDPTUnmap
>         | X64PageDirectoryMap
>         | X64PageDirectoryUnmap
>         | X64PageTableMap
>         | X64PageTableUnmap
>--       | X64IOPageTableMap
>--       | X64IOPageTableUnmap
>         | X64PageMap
>         | X64PageUnmap
>--       | X64PageMapIO
>         | X64PageGetAddress
>         | X64ASIDControlMakePool
>         | X64ASIDPoolAssign
>         | X64IOPortControlIssue
>         | X64IOPortIn8
>         | X64IOPortIn16
>         | X64IOPortIn32
>         | X64IOPortOut8
>         | X64IOPortOut16
>         | X64IOPortOut32
>         | X64IRQIssueIRQHandlerIOAPIC
>         | X64IRQIssueIRQHandlerMSI
>         deriving (Show, Eq, Enum, Bounded)

