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

> module SEL4.Object.VCPU.ARM_HYP(VCPU(..), vcpuBits, decodeARMVCPUInvocation, performARMVCPUInvocation) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Object.TCB #-}
% {-# BOOT-EXPORTS: vcpuBits VCPU() #-}

> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.API.Failures
> import {-# SOURCE #-} SEL4.Object.TCB
> import SEL4.API.InvocationLabels.ARM_HYP
> import SEL4.API.Invocation.ARM_HYP as ArchInv
> import SEL4.API.Types
> import SEL4.API.InvocationLabels

> import Data.Bits

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
>     case invocationType label of
>         ArchInvocationLabel ARMVCPUSetTCB -> error "FIXME ARMHYP TODO"
>         ArchInvocationLabel ARMVCPUInjectIRQ -> error "FIXME ARMHYP TODO"
>         ArchInvocationLabel ARMVCPUReadReg -> error "FIXME ARMHYP TODO"
>         ArchInvocationLabel ARMVCPUWriteReg -> error "FIXME ARMHYP TODO"
>         _ -> throw IllegalOperation
> decodeARMVCPUInvocation _ _ _ _ _ _ = throw IllegalOperation

%     case args of
%         [mr0, mr1] -> do
%             let vid = mr0 .&. 0xffff
%             let prio = (mr0 `shiftR` 16) .&. 0xff
%             let group = (mr0 `shiftR` 24) .&. 0xff
%             let index = mr1 .&. 0xff
%             error "ARMHYP FIXME TODO"
%         _ -> throw TruncatedMessage

% performARMVCPUInvocation i [_ from InvokeVCPU _]

> performARMVCPUInvocation :: ArchInv.Invocation -> KernelP [Word]
> performARMVCPUInvocation = error "FIXME ARMHYP TODO"

% vcpuSetTCB
% vcpuInjectIRQ
% vcpuReadRegister
% vcpuFinalise?
% vcpuInit?

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

