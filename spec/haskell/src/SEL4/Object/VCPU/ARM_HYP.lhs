%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%
FIXME ARMHYP LICENSE UPDATE?

This module defines the contents of a VCPU object used for management of
hypervisor extensions on ARM.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.VCPU.ARM_HYP(vcpuBits, decodeARMVCPUInvocation, performARMVCPUInvocation) where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.Structures.TARGET
> import SEL4.API.Failures
> import SEL4.Object.Instances()
> import SEL4.API.InvocationLabels.ARM_HYP
> import SEL4.API.Invocation
> import SEL4.API.Invocation.ARM_HYP as ArchInv
> import SEL4.API.Types
> import SEL4.API.InvocationLabels
> import SEL4.Machine.Hardware.ARM_HYP
> import {-# SOURCE #-} SEL4.Object.TCB

> import Data.Bits

\end{impdetails}

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

FIXME ARMHYP the VCPU also contains gic interface info and cpXRegs, time will tell what is actually needed for verification. The one thing we definitely need is the thread the VCPU is associated with

> decodeVCPUSetTCB :: ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation
> decodeVCPUSetTCB cap@(VCPUCap {}) extraCaps = do
>     when (null extraCaps) $ throw TruncatedMessage
>     -- FIXME ARMHYP C code calls deriveCap here before checking the cap type, discuss with kernel team
>     tcbPtr <- case fst (head extraCaps) of
>         ThreadCap tcbPtr -> return tcbPtr
>         _ -> throw IllegalOperation
>     return $ InvokeVCPU $ VCPUSetTCB (capVCPUPtr cap) tcbPtr
> decodeVCPUSetTCB _ _ = throw IllegalOperation

> decodeARMVCPUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation
> decodeARMVCPUInvocation label args capIndex slot cap@(VCPUCap {}) extraCaps =
>     case invocationType label of
>         ArchInvocationLabel ARMVCPUSetTCB ->
>             decodeVCPUSetTCB cap extraCaps
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

FIXME ARMHYP is it possible to dissociate by using VCPUSetTCB? because then I have to change the decode to set a Nothing if ptr is null, plus a bunch of signatures

> dissociateVCPUTCB :: PPtr TCB -> PPtr VCPU -> Kernel ()
> dissociateVCPUTCB tcbPtr vcpuPtr = do
>     tcbVCPU <- archThreadGet atcbVCPUPtr tcbPtr
>     vcpu <- getObject vcpuPtr
>     let vcpuTCB = vcpuTCBPtr vcpu
>     when (tcbVCPU /= Just vcpuPtr || vcpuTCB /= Just tcbPtr) $
>         fail "TCB and VCPU not associated"
>     setObject vcpuPtr $ vcpu { vcpuTCBPtr = Nothing }
>     archThreadSet (\atcb -> atcb { atcbVCPUPtr = Nothing }) tcbPtr

> associateVCPUTCB :: PPtr TCB -> PPtr VCPU -> Kernel ()
> associateVCPUTCB tcbPtr vcpuPtr = do
>     tcbVCPU <- archThreadGet atcbVCPUPtr tcbPtr
>     case tcbVCPU of Just ptr -> dissociateVCPUTCB tcbPtr ptr
>                     _ -> return ()
>     vcpu <- getObject vcpuPtr
>     case (vcpuTCBPtr vcpu) of
>         Just ptr -> dissociateVCPUTCB ptr vcpuPtr
>         _ -> return ()
>     archThreadSet (\atcb -> atcb { atcbVCPUPtr = Just vcpuPtr }) tcbPtr
>     setObject vcpuPtr $ vcpu { vcpuTCBPtr = Just tcbPtr }

> performARMVCPUInvocation :: VCPUInvocation -> Kernel ()
> performARMVCPUInvocation (VCPUSetTCB vcpuPtr tcbPtr) =
>     associateVCPUTCB tcbPtr vcpuPtr
> performARMVCPUInvocation _ = error "FIXME ARMHYP TODO"

% vcpuInjectIRQ
% vcpuReadRegister
% vcpuFinalise?
% vcpuInit?

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

