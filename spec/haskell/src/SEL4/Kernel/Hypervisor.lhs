%
% Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
%
% SPDX-License-Identifier: GPL-2.0-only
%

Some architectures/platforms have support for hypervisor mechanisms. These mechanisms can throw their own kind of fault, which must be dealt with appropriately. For non-hypervisor platforms, these functions are implemented as stubs.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Kernel.Hypervisor (handleHypervisorFault) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures SEL4.API.Failures #-}
% {-# BOOT-EXPORTS: handleHypervisorFault #-}

> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object

\end{impdetails}

The architecture-specific definitions are imported qualified with the "Arch" prefix.

> import qualified SEL4.Kernel.Hypervisor.TARGET as Arch

\subsection{Implementation-defined Functions}

This module defines architecture-specific hypervisor management procedures. The operations required are:

\begin{itemize}

\item handle hypervisor-specific faults

> handleHypervisorFault :: PPtr TCB -> HypFaultType -> Kernel ()
> handleHypervisorFault = Arch.handleHypervisorFault

