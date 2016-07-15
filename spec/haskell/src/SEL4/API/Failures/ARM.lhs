%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines the encoding of arch-specific faults.

> module SEL4.API.Failures.ARM where

\begin{impdetails}

> import SEL4.Machine

\end{impdetails}

> data ArchFault
>     = VMFault {
>             vmFaultAddress :: VPtr,
>             vmFaultArchData :: [Word] }
>     deriving Show

