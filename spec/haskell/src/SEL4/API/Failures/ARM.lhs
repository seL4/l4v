%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the encoding of arch-specific faults.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.API.Failures.ARM where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Machine

\end{impdetails}

> data ArchFault
>     = VMFault {
>             vmFaultAddress :: VPtr,
>             vmFaultArchData :: [Word] }
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     | VCPUFault {
>             vcpuHSR :: Word }
>     | VPPIEvent {
>             vppiIRQ :: IRQ }
>     | VGICMaintenance { vgicMaintenanceData :: Maybe Word }
#endif
>     deriving Show

