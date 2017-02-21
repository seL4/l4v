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

> module SEL4.Object.VCPU.ARM_HYP(vcpuBits, decodeARMVCPUInvocation, performARMVCPUInvocation, vcpuFinalise, vcpuSwitch, dissociateVCPUTCB, vgicMaintenance) where

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
> import SEL4.API.Failures.TARGET
> import {-# SOURCE #-} SEL4.Kernel.FaultHandler
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
>     tcbPtr <- case fst (head extraCaps) of
>         ThreadCap tcbPtr -> return tcbPtr
>         _ -> throw IllegalOperation
>     return $ InvokeVCPU $ VCPUSetTCB (capVCPUPtr cap) tcbPtr
> decodeVCPUSetTCB _ _ = throw IllegalOperation

It is not possible to dissociate a VCPU and a TCB by using SetTCB. Final outcome has to be an associated TCB and VCPU. The only way to get lasting dissociation is to delete the TCB or the VCPU.

> dissociateVCPUTCB :: PPtr VCPU -> PPtr TCB -> Kernel ()
> dissociateVCPUTCB vcpuPtr tcbPtr = do
>     tcbVCPU <- archThreadGet atcbVCPUPtr tcbPtr
>     vcpu <- getObject vcpuPtr
>     let vcpuTCB = vcpuTCBPtr vcpu
>     when (tcbVCPU /= Just vcpuPtr || vcpuTCB /= Just tcbPtr) $
>         fail "TCB and VCPU not associated"
>     hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
>     case hsCurVCPU of
>         Just (curVCPU, _) -> when (curVCPU == vcpuPtr) vcpuInvalidateActive
>         _ -> return ()
>     setObject vcpuPtr $ vcpu { vcpuTCBPtr = Nothing }
>     archThreadSet (\atcb -> atcb { atcbVCPUPtr = Nothing }) tcbPtr

> associateVCPUTCB :: PPtr VCPU -> PPtr TCB -> Kernel [Word]
> associateVCPUTCB vcpuPtr tcbPtr = do
>     tcbVCPU <- archThreadGet atcbVCPUPtr tcbPtr
>     case tcbVCPU of
>       Just ptr -> dissociateVCPUTCB ptr tcbPtr
>       _ -> return ()
>     vcpu <- getObject vcpuPtr
>     case (vcpuTCBPtr vcpu) of
>         Just ptr -> dissociateVCPUTCB vcpuPtr ptr
>         _ -> return ()
>     archThreadSet (\atcb -> atcb { atcbVCPUPtr = Just vcpuPtr }) tcbPtr
>     setObject vcpuPtr $ vcpu { vcpuTCBPtr = Just tcbPtr }
>     return []

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

> invokeVCPUReadReg :: PPtr VCPU -> HyperReg -> Kernel [Word]
> invokeVCPUReadReg vcpuPtr reg = do
>     ct <- getCurThread
>     hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
>     case hsCurVCPU of
>         Just (vcpuPtr, _) ->
>            vcpuCleanInvalidateActive
>         _ -> return ()
>     val <- readVCPUReg vcpuPtr reg
>     return [val]

> invokeVCPUWriteReg :: PPtr VCPU -> HyperReg -> HyperRegVal -> Kernel [Word]
> invokeVCPUWriteReg vcpuPtr reg val = do
>     hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
>     case hsCurVCPU of
>         Just (vcpuPtr, _) ->
>             vcpuCleanInvalidateActive
>         _ -> return ()
>     writeVCPUReg vcpuPtr reg val
>     return []

\subsection{VCPU: inject IRQ}

FIXME ARMHYP: this does not at this instance correspond to exactly what the C
    does, but it is the value that is stored inside of lr in the vgic

> makeVIRQ :: Word -> Word -> Word -> VIRQ
> makeVIRQ grp prio irq =
>     (grp `shiftL` groupShift) .|. (prio `shiftL` prioShift) .|. irq .|.
>         irqPending .|. eoiirqen
>     where groupShift = 30
>           prioShift = 23
>           irqPending = bit 28
>           eoiirqen = bit 19

> virqType :: Word -> Int
> virqType virq = fromIntegral $ (virq `shiftR` 28) .&. 3

> -- this is identical for pending/active/invalid VIRQs
> virqSetEOIIRQEN :: VIRQ -> Word -> VIRQ
> virqSetEOIIRQEN virq v =
>     (virq .&. complement 0x80000) .|. ((v `shiftL` 19) .&. 0x80000)

> decodeVCPUInjectIRQ :: [Word] -> ArchCapability ->
>         KernelF SyscallError ArchInv.Invocation
> decodeVCPUInjectIRQ (mr0:mr1:_) cap@(VCPUCap {}) = do
>     let vcpuPtr = capVCPUPtr cap
>     let vid = mr0 .&. 0xffff
>     let priority = (mr0 `shiftR` 16) .&. 0xff
>     let grp = (mr0 `shiftR` 24) .&. 0xff
>     let index = mr1 .&. 0xff
>
>     rangeCheck vid (0::Int) ((1 `shiftL` 10) - 1)
>     rangeCheck priority (0::Int) 31
>     rangeCheck grp (0::Int) 1
>     gic_vcpu_num_list_regs <- withoutFailure $
>         gets (armKSGICVCPUNumListRegs . ksArchState)
>     rangeCheck index 0 gic_vcpu_num_list_regs
>     vcpuLR <- withoutFailure $ liftM (vgicLR . vcpuVGIC) $ getObject vcpuPtr
>
>     when (vcpuLR ! (fromIntegral index) .&. vgicIRQMask == vgicIRQActive) $
>         throw DeleteFirst
>
>     let virq = makeVIRQ (fromIntegral grp) (fromIntegral priority) (fromIntegral vid)
>     return $ InvokeVCPU $ VCPUInjectIRQ vcpuPtr (fromIntegral index) virq
> decodeVCPUInjectIRQ _ _ = throw TruncatedMessage

> invokeVCPUInjectIRQ :: PPtr VCPU -> Int -> VIRQ -> Kernel [Word]
> invokeVCPUInjectIRQ vcpuPtr index virq = do
>     hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
>     case hsCurVCPU of
>         Just (vcpuPtr, _) ->
>             doMachineOp $ set_gic_vcpu_ctrl_lr index virq
>         _ -> do
>              vcpu <- getObject vcpuPtr
>              let vcpuLR = (vgicLR . vcpuVGIC $ vcpu) // [(index, virq)]
>              setObject vcpuPtr $ vcpu { vcpuVGIC = (vcpuVGIC vcpu) { vgicLR = vcpuLR }}
>     return []


\subsection{VCPU: perform and decode main functions}

> performARMVCPUInvocation :: VCPUInvocation -> Kernel [Word]
> performARMVCPUInvocation (VCPUSetTCB vcpuPtr tcbPtr) =
>     associateVCPUTCB vcpuPtr tcbPtr
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

\subsection{Finalisation}

For initialisation, see makeVCPUObject.

> vcpuFinalise :: PPtr VCPU -> Kernel ()
> vcpuFinalise vcpuPtr = do
>     vcpu <- getObject vcpuPtr
>     case vcpuTCBPtr vcpu of
>         Just tcbPtr -> dissociateVCPUTCB vcpuPtr tcbPtr
>         Nothing -> return ()

\subsection{VGICMaintenance}

> countTrailingZeros :: (Bits b, FiniteBits b) => b -> Int
> countTrailingZeros w =
>     length . takeWhile not . map (testBit w) $ [0 .. finiteBitSize w - 1]

> vgicMaintenance :: Kernel ()
> vgicMaintenance = do
>     eisr0 <- doMachineOp $ get_gic_vcpu_ctrl_eisr0
>     eisr1 <- doMachineOp $ get_gic_vcpu_ctrl_eisr1
>     flags <- doMachineOp $ get_gic_vcpu_ctrl_misr
>     let vgic_misr_eoi = 1 -- defined to be VGIC_HCR_EN
>
>     fault <-
>         if (flags .&. vgic_misr_eoi /= 0)
>         then
>             if (eisr0 == 0 && eisr1 == 0) -- irq_idx invalid
>                 then return $ VGICMaintenance [0, 0]
>                 else (do
>                     let irq_idx = irqIndex eisr0 eisr1
>                     gic_vcpu_num_list_regs <-
>                         gets (armKSGICVCPUNumListRegs . ksArchState)
>                     when (irq_idx < gic_vcpu_num_list_regs) (badIndex irq_idx)
>                     return $ VGICMaintenance [fromIntegral irq_idx, 1]
>                     )
>         else return $ VGICMaintenance [0, 0]
>
>     ct <- getCurThread
>     handleFault ct $ ArchFault fault
>
>     where
>         irqIndex eisr0 eisr1 =
>             if eisr0 /= 0 then countTrailingZeros eisr0
>                           else countTrailingZeros eisr1
>         badIndex irq_idx = doMachineOp $ (do
>               virq <- get_gic_vcpu_ctrl_lr irq_idx
>               set_gic_vcpu_ctrl_lr irq_idx $ virqSetEOIIRQEN virq 0
>               )

\subsection{VCPU State Control}

> vcpuEnable :: PPtr VCPU -> Kernel ()
> vcpuEnable vcpuPtr = do
>     vcpu <- getObject vcpuPtr
>     doMachineOp $ do
>         setSCTLR (vcpuSCTLR vcpu)
>         setHCR hcrVCPU
>         isb
>         set_gic_vcpu_ctrl_hcr (vgicHCR . vcpuVGIC $ vcpu)

> vcpuDisable :: Maybe (PPtr VCPU) -> Kernel ()
> vcpuDisable vcpuPtrOpt = do
>     doMachineOp dsb
>
>     case vcpuPtrOpt of
>         Just vcpuPtr -> do
>            vcpu <- getObject vcpuPtr
>            hcr <- doMachineOp get_gic_vcpu_ctrl_hcr
>            sctlr <- doMachineOp getSCTLR
>            setObject vcpuPtr $ vcpu {
>                  vcpuSCTLR = sctlr
>                , vcpuVGIC = (vcpuVGIC vcpu) { vgicHCR = hcr }
>                }
>         Nothing -> return ()
>
>     doMachineOp $ do
>         set_gic_vcpu_ctrl_hcr 0 -- VGIC off
>         isb
>         setSCTLR sctlrDefault -- S1 MMU off
>         setHCR hcrNative
>         isb

> vcpuSave :: Maybe (PPtr VCPU, Bool) -> Kernel ()
> vcpuSave (Just (vcpuPtr, active)) = do
>     doMachineOp dsb
>
>     vcpu <- getObject vcpuPtr
>
>     -- disabled vcpus already had SCTLR and HCR stored
>     (hcr, sctlr) <- if active
>                         then do
>                             sctlr <- doMachineOp getSCTLR
>                             hcr <- doMachineOp get_gic_vcpu_ctrl_hcr
>                             return (sctlr, hcr)
>                         else return (vcpuSCTLR vcpu, vgicHCR . vcpuVGIC $ vcpu)
>
>     actlr <- doMachineOp getACTLR
>     vmcr <- doMachineOp get_gic_vcpu_ctrl_vmcr
>     apr <- doMachineOp get_gic_vcpu_ctrl_apr
>
>     numListRegs <- gets (armKSGICVCPUNumListRegs . ksArchState)
>     let gicIndices = [0..numListRegs-1]
>     lrVals <- doMachineOp $ mapM get_gic_vcpu_ctrl_lr gicIndices
>     let vcpuLR = (vgicLR . vcpuVGIC $ vcpu) // zip gicIndices lrVals
>
>     setObject vcpuPtr $ vcpu {
>           vcpuSCTLR = sctlr
>         , vcpuACTLR = actlr
>         , vcpuVGIC = (vcpuVGIC vcpu) { vgicHCR = hcr
>                                      , vgicVMCR = vmcr
>                                      , vgicAPR = apr
>                                      , vgicLR = vcpuLR }
>         }
>     doMachineOp isb
> vcpuSave _ = fail "vcpuSave: no VCPU to save"

> vcpuRestore :: PPtr VCPU -> Kernel ()
> vcpuRestore vcpuPtr = do
>     -- turn off VGIC
>     doMachineOp $ set_gic_vcpu_ctrl_hcr 0
>     doMachineOp $ isb
>
>     -- restore GIC VCPU control state
>     vcpu <- getObject vcpuPtr
>     let vgic = vcpuVGIC vcpu
>
>     doMachineOp $ do
>         set_gic_vcpu_ctrl_vmcr (vgicVMCR vgic)
>         set_gic_vcpu_ctrl_apr (vgicAPR vgic)
>
>         mapM_ (uncurry set_gic_vcpu_ctrl_lr) (map (\i -> (i, (vgicLR vgic) ! i)) [0..gicVCPUMaxNumLR-1])
>
>         setACTLR (vcpuACTLR vcpu)
>
>     vcpuEnable vcpuPtr

> vcpuInvalidateActive :: Kernel ()
> vcpuInvalidateActive = do
>     hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
>     case hsCurVCPU of
>         Just (vcpuPtr, True) -> vcpuDisable Nothing
>         _ -> return ()
>     modifyArchState (\s -> s { armHSCurVCPU = Nothing })

> vcpuCleanInvalidateActive = do
>     hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
>     vcpuSave hsCurVCPU
>     vcpuInvalidateActive

> vcpuSwitch :: Maybe (PPtr VCPU) -> Kernel ()
> vcpuSwitch Nothing = do
>     hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
>     case hsCurVCPU of
>         Nothing -> return () -- both null, current can't be active
>         Just (vcpuPtr, active) -> do -- switch to thread without vcpu
>             when active $ do -- save state if not saved already
>                 vcpuDisable (Just vcpuPtr)
>                 modifyArchState (\s -> s { armHSCurVCPU = Just (vcpuPtr, False) })
>             return ()
> vcpuSwitch (Just new) = do
>     hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
>     case hsCurVCPU of
>         Nothing -> do -- switch to new VCPU with no current
>             vcpuRestore new
>             modifyArchState (\s -> s { armHSCurVCPU = Just (new, True) })
>         Just (vcpuPtr, active) -> do -- switch from an existing VCPU
>             if vcpuPtr /= new
>                 then do -- different VCPU
>                     vcpuSave hsCurVCPU
>                     vcpuRestore new
>                     modifyArchState (\s -> s { armHSCurVCPU = Just (new, True) })
>                 else do -- same VCPU: switch to active
>                     when (not active) $ do
>                         doMachineOp isb
>                         vcpuEnable new
>                         modifyArchState (\s -> s { armHSCurVCPU = Just (new, True) })

#endif /* CONFIG_ARM_HYPERVISOR_SUPPORT */

