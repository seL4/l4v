%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines the contents of a VCPU object used for management of
hypervisor extensions on ARM.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.VCPU.ARM_HYP(VCPU(), vcpuBits) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Object.TCB #-}
% {-# BOOT-EXPORTS: vcpuBits VCPU() #-}

> import SEL4.Machine
> import {-# SOURCE #-} SEL4.Object.TCB

%> import SEL4.API.Failures

\end{impdetails}

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

FIXME ARMHYP the VCPU also contains gic interface info and cpXRegs, time will tell what is actually needed for verification. The one thing we definitely need is the thread the VCPU is associated with

> data VCPU = VCPUObj {
>                 vcpuTCBPtr :: PPtr TCB
>             }

> vcpuBits = pageBits :: Int

> decodeARMVCPUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation
> decodeARMVCPUInvocation label args capIndex slot cap@(VCPUCap {}) extraCaps =
>     case args of
>         [mr0, mr1] -> do
>             let vid = mr0 .&. 0xffff
>             let prio = (mr0 `shiftR` 16) .&. 0xff
>             let group = (mr0 `shiftR` 24) .&. 0xff
>             let index = mr1 .&. 0xff
>             FIXME TODO
>         _ -> throw TruncatedMessage

> decodeARMVCPUInvocation ARMVCPUSetTCB args capIndex slot cap@(VCPUCap {}) extraCaps =

> decodeARMVCPUInvocation ARMVCPUInjectIRQ args capIndex slot cap@(VCPUCap {}) _ =

> decodeARMVCPUInvocation ARMVCPUReadReg args capIndex slot cap@(VCPUCap {}) _ =

> decodeARMVCPUInvocation ARMVCPUWriteReg args capIndex slot cap@(VCPUCap {}) _ =

> decodeARMVCPUInvocation _ = throw IllegalOperation




> performARMVCPUInvocation i [_ from InvokeVCPU _]
>

> vcpuSetTCB
> vcpuInjectIRQ
> vcpuReadRegister
> vcpuFinalise?
> vcpuInit?
>

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

