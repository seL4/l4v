%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module is exported to the simulator interface to allow it to access target-dependent definitions.

> {-# LANGUAGE CPP #-}

> module SEL4.Machine.Target (
>         module SEL4.Machine.Hardware.TARGET,
>         module SEL4.Machine.RegisterSet.TARGET
>     ) where
>
> import SEL4.Machine.Hardware.TARGET
> import SEL4.Machine.RegisterSet.TARGET

