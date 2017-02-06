%
% Copyright 2016, Data61, CSIRO
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(DATA61_GPL)
%

This module defines the encoding of arch-specific faults.

> {-# LANGUAGE CPP #-}
> module SEL4.API.Faults.ARM where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.TCB(asUser)
> import Data.Bits

\end{impdetails}

> import SEL4.API.Failures.ARM

> makeArchFaultMessage :: ArchFault -> PPtr TCB -> Kernel (Word, [Word])
> makeArchFaultMessage (VMFault vptr archData) thread = do
>     pc <- asUser thread getRestartPC
>     return (5, pc:fromVPtr vptr:archData)

> handleArchFaultReply :: ArchFault -> PPtr TCB -> Word -> [Word] -> Kernel Bool
> handleArchFaultReply (VMFault {}) _ _ _ = return True

