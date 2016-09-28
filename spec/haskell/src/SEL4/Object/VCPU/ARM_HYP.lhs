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
> import SEL4.Machine.Hardware.ARM_HYP
> import SEL4.Model.StateData.TARGET
> import SEL4.API.Failures
> import SEL4.Object.Instances()
> import SEL4.API.InvocationLabels.ARM_HYP
> import SEL4.API.Invocation
> import SEL4.API.Invocation.ARM_HYP as ArchInv
> import SEL4.API.Types
> import SEL4.API.InvocationLabels
> import {-# SOURCE #-} SEL4.Object.TCB
> import {-# SOURCE #-} SEL4.Kernel.Thread

> import Data.Bits
> import Data.Word(Word8, Word16, Word32)
> import Data.Array

\end{impdetails}

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

FIXME ARMHYP the VCPU also contains gic interface info and cpXRegs, time will tell what is actually needed for verification. The one thing we definitely need is the thread the VCPU is associated with

\subsection{VCPU: Set TCB}

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

It is not possible to dissociate a VCPU and a TCB by using SetTCB. Final outcome has to be an associated TCB and VCPU. The only way to get lasting dissociation is to delete the TCB or the VCPU.

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
>     case tcbVCPU of
>       Just ptr -> dissociateVCPUTCB tcbPtr ptr
>       _ -> return ()
>     vcpu <- getObject vcpuPtr
>     case (vcpuTCBPtr vcpu) of
>         Just ptr -> dissociateVCPUTCB ptr vcpuPtr
>         _ -> return ()
>     archThreadSet (\atcb -> atcb { atcbVCPUPtr = Just vcpuPtr }) tcbPtr
>     setObject vcpuPtr $ vcpu { vcpuTCBPtr = Just tcbPtr }

\subsection{VCPU: Read/Write Registers}

Currently, there is only one VCPU register available for reading/writing by the user: cpx.sctlr.

> decodeVCPUReadReg :: [Word] -> ArchCapability ->
>         KernelF SyscallError ArchInv.Invocation
> decodeVCPUReadReg (field:_) cap@(VCPUCap {}) = do
>     when (field /= 0) $ throw (InvalidArgument 1)
>     return $ InvokeVCPU $
>         VCPUReadRegister (capVCPUPtr cap) (fromIntegral field)
> decodeVCPUReadReg _ _ = throw TruncatedMessage

> decodeVCPUWriteReg :: [Word] -> ArchCapability ->
>         KernelF SyscallError ArchInv.Invocation
> decodeVCPUWriteReg (field:val:_) cap@(VCPUCap {}) = do
>     when (field /= 0) $ throw (InvalidArgument 1)
>     return $ InvokeVCPU $ VCPUWriteRegister (capVCPUPtr cap)
>                 (fromIntegral field) (fromIntegral val)
> decodeVCPUWriteReg _ _ = throw TruncatedMessage

> readVCPUReg :: PPtr VCPU -> HyperReg -> Kernel HyperRegVal
> readVCPUReg vcpuPtr reg = do
>     if reg == 0
>         then do
>             vcpu <- getObject vcpuPtr
>             return $ vcpuSCTLR vcpu
>         else fail "VCPU register out of range"

> writeVCPUReg :: PPtr VCPU -> HyperReg -> HyperRegVal -> Kernel ()
> writeVCPUReg vcpuPtr reg val =
>     if reg == 0
>         then do
>             vcpu <- getObject vcpuPtr
>             setObject vcpuPtr $ vcpu { vcpuSCTLR = val }
>         else fail "VCPU register out of range"

> invokeVCPUReadReg :: PPtr VCPU -> HyperReg -> Kernel ()
> invokeVCPUReadReg vcpuPtr reg = do
>     ct <- getCurThread
>     val <- readVCPUReg vcpuPtr reg
>     asUser ct $ setRegister (msgRegisters !! 0) $ fromIntegral val
>     let msgInfo = MI {
>             msgLabel = 0,
>             msgCapsUnwrapped = 0,
>             msgExtraCaps = 0,
>             msgLength = 1 }
>     setMessageInfo ct msgInfo
>     -- prevent kernel from generating a reply to ct since we already did
>     setThreadState Running ct

> invokeVCPUWriteReg :: PPtr VCPU -> HyperReg -> HyperRegVal -> Kernel ()
> invokeVCPUWriteReg vcpuPtr reg val = writeVCPUReg vcpuPtr reg val

\subsection{VCPU: inject IRQ}

FIXME ARMHYP: this does not at this instance correspond to exactly what the C
    does, but it is the value that is stored inside of lr in the vgic

> makeVIRQ :: Word32 -> Word32 -> Word32 -> VIRQ
> makeVIRQ group prio irq =
>     (group `shiftL` groupShift) .|. (prio `shiftL` prioShift) .|. irq .|.
>         irqPending .|. eoiirqen
>     where groupShift = 30
>           prioShift = 23
>           irqPending = bit 28
>           eoiirqen = bit 19

> decodeVCPUInjectIRQ :: [Word] -> ArchCapability ->
>         KernelF SyscallError ArchInv.Invocation
> decodeVCPUInjectIRQ (mr0:mr1:_) cap@(VCPUCap {}) = do
>     let vcpuPtr = capVCPUPtr cap
>     let vid = mr0 .&. 0xffff
>     let priority = (mr0 `shiftR` 16) .&. 0xff
>     let group = (mr0 `shiftR` 24) .&. 0xff
>     let index = mr1 .&. 0xff
>
>     rangeCheck vid (0::Int) ((1 `shiftL` 10) - 1)
>     rangeCheck priority (0::Int) 31
>     rangeCheck group (0::Int) 1
>     gic_vcpu_num_list_regs <- withoutFailure $
>         gets (armKSGICVCPUNumListRegs . ksArchState)
>     rangeCheck index 0 gic_vcpu_num_list_regs
>     vcpuLR <- withoutFailure $ liftM (vgicLR . vcpuVGIC) $ getObject vcpuPtr
>
>     when (vcpuLR ! (fromIntegral index) .&. vgicIRQMask == vgicIRQActive) $
>         throw DeleteFirst
>
>     let virq = makeVIRQ (fromIntegral group) (fromIntegral priority) (fromIntegral vid)
>     return $ InvokeVCPU $ VCPUInjectIRQ vcpuPtr (fromIntegral index) virq
> decodeVCPUInjectIRQ _ _ = throw TruncatedMessage

> invokeVCPUInjectIRQ :: PPtr VCPU -> Int -> VIRQ -> Kernel ()
> invokeVCPUInjectIRQ vcpuPtr index virq = do
>     vcpu <- getObject vcpuPtr
>     let vcpuLR = (vgicLR . vcpuVGIC $ vcpu) // [(index, virq)]
>     setObject vcpuPtr $ vcpu { vcpuVGIC = (vcpuVGIC vcpu) { vgicLR = vcpuLR }}


\subsection{VCPU: perform and decode main functions}

> performARMVCPUInvocation :: VCPUInvocation -> Kernel ()
> performARMVCPUInvocation (VCPUSetTCB vcpuPtr tcbPtr) =
>     associateVCPUTCB tcbPtr vcpuPtr
> performARMVCPUInvocation (VCPUReadRegister vcpuPtr reg) =
>     invokeVCPUReadReg vcpuPtr reg
> performARMVCPUInvocation (VCPUWriteRegister vcpuPtr reg val) =
>     invokeVCPUWriteReg vcpuPtr reg val
> performARMVCPUInvocation (VCPUInjectIRQ vcpuPtr index virq) =
>     invokeVCPUInjectIRQ vcpuPtr index virq

> decodeARMVCPUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         ArchCapability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError ArchInv.Invocation
> decodeARMVCPUInvocation label args capIndex slot cap@(VCPUCap {}) extraCaps =
>     case invocationType label of
>         ArchInvocationLabel ARMVCPUSetTCB ->
>             decodeVCPUSetTCB cap extraCaps
>         ArchInvocationLabel ARMVCPUReadReg ->
>             decodeVCPUReadReg args cap
>         ArchInvocationLabel ARMVCPUWriteReg ->
>             decodeVCPUWriteReg args cap
>         ArchInvocationLabel ARMVCPUInjectIRQ ->
>             decodeVCPUInjectIRQ args cap
>         _ -> throw IllegalOperation
> decodeARMVCPUInvocation _ _ _ _ _ _ = throw IllegalOperation

% FIXME ARMHYP TODO
% vcpuFinalise?
% vcpuInit?
% vcpuSwitch? vcpuRestore?
% vcpuSave/Restore?

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

