%
% Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
%
% SPDX-License-Identifier: GPL-2.0-only
%

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Kernel.Hypervisor.ARM where

\begin{impdetails}

> import SEL4.Machine (PPtr (..))
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.API.Failures
> import SEL4.Kernel.FaultHandler
> import SEL4.API.Failures.TARGET
> import SEL4.Machine.Hardware.TARGET

\end{impdetails}

> handleHypervisorFault :: PPtr TCB -> HypFaultType -> Kernel ()
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> handleHypervisorFault thread (ARMVCPUFault hsr) = do
>     handleFault thread (ArchFault $ VCPUFault $ fromIntegral hsr)
#else
> handleHypervisorFault _ (ARMNoHypFaults) =
>     -- no hypervisor faults on this platform
>     return ()
#endif

