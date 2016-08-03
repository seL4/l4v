%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines arch-specific kernel entry/exit hooks.

> module SEL4.API.Syscall.ARM where

\begin{impdetails}

> import SEL4.Model.StateData

\end{impdetails}

\subsection{ARM-Specific Kernel Entry/Exit Hooks}

> cEntryHook :: Kernel ()
> cEntryHook = return ()
>
> cExitHook :: Kernel ()
> cExitHook = return ()



