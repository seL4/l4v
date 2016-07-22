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

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.API.Failures.ARM_HYP where

\begin{impdetails}

> import SEL4.Machine

\end{impdetails}

FIXME ARMHYP VCPU and VGIC faults should be handled here

> data ArchFault
>     = VMFault {
>             vmFaultAddress :: VPtr,
>             vmFaultArchData :: [Word] }
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     | VCPUFault {
>             vcpuHSR :: Word }
>     | VGICMaintenance { vgicMaintenanceData :: [Word] }
#endif
>     deriving Show

