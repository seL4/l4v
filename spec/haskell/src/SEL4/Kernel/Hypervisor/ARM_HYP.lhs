%
% Copyright 2016, Data61, CSIRO
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Kernel.Hypervisor.ARM_HYP where

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

