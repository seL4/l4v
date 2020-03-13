%
% Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
%
% SPDX-License-Identifier: GPL-2.0-only
%

The X64 target does not have any hypervisor support.

> module SEL4.Kernel.Hypervisor.X64 where

\begin{impdetails}

> import SEL4.Machine (PPtr(..))
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Machine.Hardware.X64 (HypFaultType(..))

\end{impdetails}

> handleHypervisorFault :: PPtr TCB -> HypFaultType -> Kernel ()
> handleHypervisorFault _ (X64NoHypFaults) = return ()

