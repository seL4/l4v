%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the encoding of arch-specific faults.

> module SEL4.API.Failures.X64 where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine

\end{impdetails}

> data ArchFault
>     = VMFault {
>             vmFaultAddress :: VPtr,
>             vmFaultArchData :: [Word] }
>     deriving Show

