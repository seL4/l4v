%
% Copyright 2016, Data61, CSIRO
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(DATA61_GPL)
%

The ARM target does not have any hypervisor support.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Kernel.Hypervisor.ARM where

\begin{impdetails}

> import SEL4.Machine (PPtr(..))
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Machine.Hardware.ARM (HypFaultType(..))

\end{impdetails}

> handleHypervisorFault :: PPtr TCB -> HypFaultType -> Kernel ()
> handleHypervisorFault _ (ARMNoHypFaults) = return ()

