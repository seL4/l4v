%
% Copyright 2016, Data61, CSIRO
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

FIXME ARMHYP TODO handleHypervisorFault

> module SEL4.Kernel.Hypervisor.ARM_HYP where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Machine.Hardware.ARM_HYP as Arch

\end{impdetails}

> handleHypervisorFault :: PPtr TCB -> Arch.HypFaultType -> Kernel ()
> handleHypervisorFault _ Arch.ARMNoHypFaults = fail "FIXME ARMHYP handleHypervisorFault"

