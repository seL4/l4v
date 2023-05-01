--
-- Copyright 2022, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module defines the contents of a VCPU object used for management of
-- hypervisor extensions on AArch64.

-- Note for AARCH64: most of these functions in C are common between 32 and 64
-- bit Arm platforms (src/arch/arm/object/vcpu.c), and so end up identical to
-- ARM_HYP verification platform

{-# LANGUAGE CPP #-}

module SEL4.Object.VCPU.AARCH64(curVCPUActive, vcpuBits, decodeARMVCPUInvocation, performARMVCPUInvocation, vcpuFinalise, vcpuSwitch, dissociateVCPUTCB, vgicMaintenance, vppiEvent, irqVPPIEventIndex) where

import Prelude hiding (Word)
import SEL4.Machine
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Object.Structures.TARGET
import SEL4.Machine.Hardware.AARCH64 hiding (MachineMonad, IRQ, maskInterrupt)
import SEL4.Model.StateData.TARGET
import SEL4.API.Failures
import SEL4.Object.Instances()
import SEL4.API.InvocationLabels.AARCH64
import SEL4.API.Invocation
import SEL4.API.Invocation.AARCH64 as ArchInv
import SEL4.Machine.RegisterSet.AARCH64 (Register(..), VCPUReg(..), vcpuRegNum, vcpuRegSavedWhenDisabled)
import SEL4.API.Types
import SEL4.API.InvocationLabels
import SEL4.API.Failures.TARGET
import SEL4.Machine.Hardware.AARCH64.PLATFORM (irqVTimerEvent)
import {-# SOURCE #-} SEL4.Kernel.FaultHandler
import {-# SOURCE #-} SEL4.Object.TCB
import {-# SOURCE #-} SEL4.Kernel.Thread
import {-# SOURCE #-} SEL4.Object.Interrupt

import Data.Bits hiding (countTrailingZeros)
import Data.Word(Word8, Word16, Word32, Word64)
import Data.WordLib(countTrailingZeros)
import Data.Array
import Data.Maybe

{- VCPU: Helper functions -}

-- FIXME: make this a Reader Monad when we move to MCS
curVCPUActive :: Kernel Bool
curVCPUActive = do
    vcpu <- gets (armHSCurVCPU . ksArchState)
    return $ isJust vcpu && snd (fromJust vcpu)

{- VCPU: Set TCB -}

decodeVCPUSetTCB :: ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeVCPUSetTCB cap@(VCPUCap {}) extraCaps = do
    when (null extraCaps) $ throw TruncatedMessage
    tcbPtr <- case fst (head extraCaps) of
        ThreadCap tcbPtr -> return tcbPtr
        _ -> throw IllegalOperation
    return $ InvokeVCPU $ VCPUSetTCB (capVCPUPtr cap) tcbPtr
decodeVCPUSetTCB _ _ = throw IllegalOperation

-- It is not possible to dissociate a VCPU and a TCB by using SetTCB. Final
-- outcome has to be an associated TCB and VCPU. The only way to get lasting
-- dissociation is to delete the TCB or the VCPU.

dissociateVCPUTCB :: PPtr VCPU -> PPtr TCB -> Kernel ()
dissociateVCPUTCB vcpuPtr tcbPtr = do
    tcbVCPU <- archThreadGet atcbVCPUPtr tcbPtr
    vcpu <- getObject vcpuPtr
    let vcpuTCB = vcpuTCBPtr vcpu
    when (tcbVCPU /= Just vcpuPtr || vcpuTCB /= Just tcbPtr) $
        fail "TCB and VCPU not associated"
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    case hsCurVCPU of
        Just (curVCPU, _) -> when (curVCPU == vcpuPtr) vcpuInvalidateActive
        _ -> return ()
    archThreadSet (\atcb -> atcb { atcbVCPUPtr = Nothing }) tcbPtr
    setObject vcpuPtr $ vcpu { vcpuTCBPtr = Nothing }
    asUser tcbPtr $ (do
        cpsr <- getRegister (Register SPSR_EL1)
        setRegister (Register SPSR_EL1) $ sanitiseRegister False (Register SPSR_EL1) cpsr
        )

associateVCPUTCB :: PPtr VCPU -> PPtr TCB -> Kernel [Word]
associateVCPUTCB vcpuPtr tcbPtr = do
    tcbVCPU <- archThreadGet atcbVCPUPtr tcbPtr
    case tcbVCPU of
      Just ptr -> dissociateVCPUTCB ptr tcbPtr
      _ -> return ()
    vcpu <- getObject vcpuPtr
    case (vcpuTCBPtr vcpu) of
        Just ptr -> dissociateVCPUTCB vcpuPtr ptr
        _ -> return ()
    archThreadSet (\atcb -> atcb { atcbVCPUPtr = Just vcpuPtr }) tcbPtr
    setObject vcpuPtr $ vcpu { vcpuTCBPtr = Just tcbPtr }
    ct <- getCurThread
    when (tcbPtr == ct) $ vcpuSwitch (Just vcpuPtr)
    return []

{- VCPU: Update functions -}

vcpuUpdate :: PPtr VCPU -> (VCPU -> VCPU) -> Kernel ()
vcpuUpdate vcpuPtr f = do
    vcpu <- getObject vcpuPtr
    setObject vcpuPtr (f vcpu)

vgicUpdate :: PPtr VCPU -> (GICVCPUInterface -> GICVCPUInterface) -> Kernel ()
vgicUpdate vcpuPtr f = vcpuUpdate vcpuPtr (\vcpu -> vcpu { vcpuVGIC = f (vcpuVGIC vcpu) })

vgicUpdateLR :: PPtr VCPU -> Int -> VIRQ -> Kernel ()
vgicUpdateLR vcpuPtr irq_idx virq =
    vgicUpdate vcpuPtr (\vgic -> vgic { vgicLR = (vgicLR vgic) // [(irq_idx, virq)] })

{- VCPU: Read/Write Registers -}

decodeVCPUReadReg :: [Word] -> ArchCapability ->
        KernelF SyscallError ArchInv.Invocation
decodeVCPUReadReg (field:_) cap@(VCPUCap {}) = do
    let reg = fromIntegral field
    when (reg > (fromEnum (maxBound :: VCPUReg))) $ throw (InvalidArgument 1)
    return $ InvokeVCPU $
        VCPUReadRegister (capVCPUPtr cap) (toEnum reg)
decodeVCPUReadReg _ _ = throw TruncatedMessage

decodeVCPUWriteReg :: [Word] -> ArchCapability ->
        KernelF SyscallError ArchInv.Invocation
decodeVCPUWriteReg (field:val:_) cap@(VCPUCap {}) = do
    let reg = fromIntegral field
    when (reg > (fromEnum (maxBound :: VCPUReg))) $ throw (InvalidArgument 1)
    return $ InvokeVCPU $ VCPUWriteRegister (capVCPUPtr cap)
                (toEnum reg) (fromIntegral val)
decodeVCPUWriteReg _ _ = throw TruncatedMessage

vcpuSaveReg :: PPtr VCPU -> HyperReg -> Kernel ()
vcpuSaveReg vcpuPtr reg = do
    assert (vcpuPtr /= 0) "vcpuSaveReg: no VCPU provided"
    val <- doMachineOp $ readVCPUHardwareReg reg
    vcpuUpdate vcpuPtr (\vcpu -> vcpu { vcpuRegs =  vcpuRegs vcpu // [(reg, val)] })

vcpuSaveRegRange :: PPtr VCPU -> HyperReg -> HyperReg -> Kernel ()
vcpuSaveRegRange vcpuPtr regStart regEnd =
    mapM_ (\reg -> vcpuSaveReg vcpuPtr reg) [regStart .. regEnd]

vcpuRestoreReg :: PPtr VCPU -> HyperReg -> Kernel ()
vcpuRestoreReg vcpuPtr reg = do
    assert (vcpuPtr /= 0) "vcpuRestoreReg: no VCPU provided"
    vcpu <- getObject vcpuPtr
    doMachineOp $ writeVCPUHardwareReg reg (vcpuRegs vcpu ! reg)

vcpuRestoreRegRange :: PPtr VCPU -> HyperReg -> HyperReg -> Kernel ()
vcpuRestoreRegRange vcpuPtr regStart regEnd =
    mapM_ (\reg -> vcpuRestoreReg vcpuPtr reg) [regStart .. regEnd]

vcpuReadReg :: PPtr VCPU -> HyperReg -> Kernel HyperRegVal
vcpuReadReg vcpuPtr reg = do
    assert (vcpuPtr /= 0) "vcpuReadReg: no VCPU provided"
    vcpu <- getObject vcpuPtr
    return $ vcpuRegs vcpu ! reg

vcpuWriteReg :: PPtr VCPU -> HyperReg -> HyperRegVal -> Kernel ()
vcpuWriteReg vcpuPtr reg val = do
    assert (vcpuPtr /= 0) "vcpuWriteReg: no VCPU provided"
    vcpuUpdate vcpuPtr (\vcpu -> vcpu { vcpuRegs = vcpuRegs vcpu // [(reg, val)] })

readVCPUReg :: PPtr VCPU -> HyperReg -> Kernel HyperRegVal
readVCPUReg vcpuPtr reg = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    (onCurVCPU, active) <- return $ case hsCurVCPU of
        Just (curVCPU, a) -> (curVCPU == vcpuPtr, a)
        _ -> (False, False)

    if onCurVCPU
        then if vcpuRegSavedWhenDisabled reg && not active
                then vcpuReadReg vcpuPtr reg
                else doMachineOp $ readVCPUHardwareReg reg
        else vcpuReadReg vcpuPtr reg

writeVCPUReg :: PPtr VCPU -> HyperReg -> HyperRegVal -> Kernel ()
writeVCPUReg vcpuPtr reg val = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    (onCurVCPU, active) <- return $ case hsCurVCPU of
        Just (curVCPU, a) -> (curVCPU == vcpuPtr, a)
        _ -> (False, False)

    if onCurVCPU
        then if vcpuRegSavedWhenDisabled reg && not active
                then vcpuWriteReg vcpuPtr reg val
                else doMachineOp $ writeVCPUHardwareReg reg val
        else vcpuWriteReg vcpuPtr reg val

invokeVCPUReadReg :: PPtr VCPU -> HyperReg -> Kernel [Word]
invokeVCPUReadReg vcpuPtr reg = do
    ct <- getCurThread
    val <- readVCPUReg vcpuPtr reg
    return [val]

invokeVCPUWriteReg :: PPtr VCPU -> HyperReg -> HyperRegVal -> Kernel [Word]
invokeVCPUWriteReg vcpuPtr reg val = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    writeVCPUReg vcpuPtr reg val
    return []

{- VCPU: inject IRQ -}

-- analogous to virq_virq_pending_new in C, with virqEOIIRQEN set
makeVIRQ :: Word -> Word -> Word -> VIRQ
makeVIRQ grp prio irq =
    ((grp .&. 1) `shiftL` groupShift) .|. ((prio .&. 0x1F) `shiftL` prioShift) .|.
    (irq .&. 0x3FF) .|. irqPending .|. eoiirqen
    where groupShift = 30
          prioShift = 23
          irqPending = bit 28
          eoiirqen = bit 19

virqType :: Word -> Int
virqType virq = fromIntegral $ (virq `shiftR` 28) .&. 3

-- combination of virq_get_virqType and virq_virq_active
isVIRQActive :: VIRQ -> Bool
isVIRQActive virq = virqType virq == 2

-- identical for pending/active/invalid VIRQs
-- there is no virq type == 3, so do nothing, as per VGICMaintenance in C
virqSetEOIIRQEN :: VIRQ -> Word -> VIRQ
virqSetEOIIRQEN virq v =
    if virqType virq == 3
    then virq
    else (virq .&. complement 0x80000) .|. ((v `shiftL` 19) .&. 0x80000)

decodeVCPUInjectIRQ :: [Word] -> ArchCapability ->
        KernelF SyscallError ArchInv.Invocation
decodeVCPUInjectIRQ (mr0:_) cap@(VCPUCap {}) = do
    let vcpuPtr = capVCPUPtr cap
    let vid = mr0 .&. 0xffff
    let priority = (mr0 `shiftR` 16) .&. 0xff
    let grp = (mr0 `shiftR` 24) .&. 0xff
    let index = (mr0 `shiftR` 32) .&. 0xff

    rangeCheck vid (0::Int) ((1 `shiftL` 10) - 1)
    rangeCheck priority (0::Int) 31
    rangeCheck grp (0::Int) 1
    gic_vcpu_num_list_regs <- withoutFailure $
        gets (armKSGICVCPUNumListRegs . ksArchState)

    when (index >= fromIntegral gic_vcpu_num_list_regs) $
       (throw $ RangeError 0 (fromIntegral gic_vcpu_num_list_regs - 1))

    vcpuLR <- withoutFailure $ liftM (vgicLR . vcpuVGIC) $ getObject vcpuPtr

    when (isVIRQActive (vcpuLR ! (fromIntegral index))) $
        throw DeleteFirst

    let virq = makeVIRQ (fromIntegral grp) (fromIntegral priority) (fromIntegral vid)
    return $ InvokeVCPU $ VCPUInjectIRQ vcpuPtr (fromIntegral index) virq
decodeVCPUInjectIRQ _ _ = throw TruncatedMessage

invokeVCPUInjectIRQ :: PPtr VCPU -> Int -> VIRQ -> Kernel [Word]
invokeVCPUInjectIRQ vcpuPtr index virq = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    if (isJust hsCurVCPU && fst (fromJust hsCurVCPU) == vcpuPtr)
      then doMachineOp $ set_gic_vcpu_ctrl_lr (fromIntegral index) virq
      else vgicUpdateLR vcpuPtr index virq
    return []

{- VCPU: acknowledge VPPI -}

decodeVCPUAckVPPI :: [Word] -> ArchCapability ->
        KernelF SyscallError ArchInv.Invocation
decodeVCPUAckVPPI (mr0:_) cap@(VCPUCap {}) = do
    let vcpuPtr = capVCPUPtr cap
    rangeCheck mr0 (fromEnum minIRQ) (fromEnum maxIRQ)
    let irq = toEnum (fromIntegral mr0) :: IRQ
    case irqVPPIEventIndex irq of
        Nothing -> throw $ InvalidArgument 0
        Just vppi -> return $ InvokeVCPU $ VCPUAckVPPI vcpuPtr vppi
decodeVCPUAckVPPI _ _ = throw TruncatedMessage

invokeVCPUAckVPPI :: PPtr VCPU -> VPPIEventIRQ -> Kernel [Word]
invokeVCPUAckVPPI vcpuPtr vppi = do
    vcpuUpdate vcpuPtr (\vcpu -> vcpu { vcpuVPPIMasked = f (vcpuVPPIMasked vcpu) })
    return []
    where f = (\masked -> masked // [(vppi, False)])

{- VCPU: perform and decode main functions -}

performARMVCPUInvocation :: VCPUInvocation -> Kernel [Word]
performARMVCPUInvocation (VCPUSetTCB vcpuPtr tcbPtr) =
    associateVCPUTCB vcpuPtr tcbPtr
performARMVCPUInvocation (VCPUReadRegister vcpuPtr reg) =
    invokeVCPUReadReg vcpuPtr reg
performARMVCPUInvocation (VCPUWriteRegister vcpuPtr reg val) =
    invokeVCPUWriteReg vcpuPtr reg val
performARMVCPUInvocation (VCPUInjectIRQ vcpuPtr index virq) =
    invokeVCPUInjectIRQ vcpuPtr index virq
performARMVCPUInvocation (VCPUAckVPPI vcpuPtr vppi) =
    invokeVCPUAckVPPI vcpuPtr vppi

decodeARMVCPUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeARMVCPUInvocation label args capIndex slot cap@(VCPUCap {}) extraCaps =
    case invocationType label of
        ArchInvocationLabel ARMVCPUSetTCB ->
            decodeVCPUSetTCB cap extraCaps
        ArchInvocationLabel ARMVCPUReadReg ->
            decodeVCPUReadReg args cap
        ArchInvocationLabel ARMVCPUWriteReg ->
            decodeVCPUWriteReg args cap
        ArchInvocationLabel ARMVCPUInjectIRQ ->
            decodeVCPUInjectIRQ args cap
        ArchInvocationLabel ARMVCPUAckVPPI ->
            decodeVCPUAckVPPI args cap
        _ -> throw IllegalOperation
decodeARMVCPUInvocation _ _ _ _ _ _ = throw IllegalOperation

{- Finalisation -}

-- For initialisation, see makeVCPUObject.

vcpuFinalise :: PPtr VCPU -> Kernel ()
vcpuFinalise vcpuPtr = do
    vcpu <- getObject vcpuPtr
    case vcpuTCBPtr vcpu of
        Just tcbPtr -> dissociateVCPUTCB vcpuPtr tcbPtr
        Nothing -> return ()

{- VCPU State Control -}

saveVirtTimer :: PPtr VCPU -> Kernel ()
saveVirtTimer vcpuPtr = do
    vcpuSaveReg vcpuPtr VCPURegCNTV_CTL
    doMachineOp $ writeVCPUHardwareReg VCPURegCNTV_CTL 0
    vcpuSaveReg vcpuPtr VCPURegCNTV_CVAL
    vcpuSaveReg vcpuPtr VCPURegCNTVOFF
    vcpuSaveReg vcpuPtr VCPURegCNTKCTL_EL1
    doMachineOp check_export_arch_timer
    cntpct <- doMachineOp read_cntpct
    vcpuUpdate vcpuPtr (\vcpu -> vcpu { vcpuVTimer = VirtTimer cntpct })

restoreVirtTimer :: PPtr VCPU -> Kernel ()
restoreVirtTimer vcpuPtr = do
    vcpuRestoreReg vcpuPtr VCPURegCNTV_CVAL
    vcpuRestoreReg vcpuPtr VCPURegCNTKCTL_EL1

    current_cntpct <- doMachineOp read_cntpct
    vcpu <- getObject vcpuPtr
    let lastPCount =  vtimerLastPCount (vcpuVTimer vcpu)
    let pcountDelta = current_cntpct - lastPCount
    cntvoff <- vcpuReadReg vcpuPtr VCPURegCNTVOFF
    let offset = cntvoff + fromIntegral pcountDelta
    vcpuWriteReg vcpuPtr VCPURegCNTVOFF offset
    vcpuRestoreReg vcpuPtr VCPURegCNTVOFF

    let vppi = fromJust $ irqVPPIEventIndex (IRQ irqVTimerEvent)
    let masked = (vcpuVPPIMasked vcpu) ! vppi
    safeToUnmask <- isIRQActive (IRQ irqVTimerEvent)
    when safeToUnmask $ doMachineOp $ maskInterrupt masked (IRQ irqVTimerEvent)
    vcpuRestoreReg vcpuPtr VCPURegCNTV_CTL

vcpuEnable :: PPtr VCPU -> Kernel ()
vcpuEnable vcpuPtr = do
    vcpuRestoreReg vcpuPtr VCPURegSCTLR
    vcpu <- getObject vcpuPtr
    doMachineOp $ do
        setHCR hcrVCPU
        isb
        set_gic_vcpu_ctrl_hcr (vgicHCR . vcpuVGIC $ vcpu)
    vcpuRestoreReg vcpuPtr VCPURegCPACR -- FPU
    restoreVirtTimer vcpuPtr

vcpuDisable :: Maybe (PPtr VCPU) -> Kernel ()
vcpuDisable vcpuPtrOpt = do
    doMachineOp dsb

    case vcpuPtrOpt of
        Just vcpuPtr -> do
           hcr <- doMachineOp get_gic_vcpu_ctrl_hcr
           vgicUpdate vcpuPtr (\vgic -> vgic { vgicHCR = hcr })
           vcpuSaveReg vcpuPtr VCPURegSCTLR
           vcpuSaveReg vcpuPtr VCPURegCPACR -- since FPU enabled
           doMachineOp isb
        Nothing -> return ()

    doMachineOp $ do
        set_gic_vcpu_ctrl_hcr 0 -- VGIC off
        isb
        setSCTLR sctlrDefault -- S1 MMU off
        isb
        setHCR hcrNative
        isb
        -- allow FPU instructions in EL0 and EL1 for native threads
        enableFpuEL01

    case vcpuPtrOpt of
        Just vcpuPtr -> do
            saveVirtTimer vcpuPtr
            doMachineOp $ maskInterrupt True (IRQ irqVTimerEvent)
        Nothing -> return ()

armvVCPUSave :: PPtr VCPU -> Bool -> Kernel ()
armvVCPUSave vcpuPtr active = do
    vcpuSaveRegRange vcpuPtr VCPURegTTBR0 VCPURegSPSR_EL1
    doMachineOp isb

vcpuSave :: Maybe (PPtr VCPU, Bool) -> Kernel ()
vcpuSave (Just (vcpuPtr, active)) = do
    doMachineOp dsb

    -- disabled vcpus already had SCTLR and HCR stored
    when active $ do
          vcpuSaveReg vcpuPtr VCPURegSCTLR
          hcr <- doMachineOp get_gic_vcpu_ctrl_hcr
          vgicUpdate vcpuPtr (\vgic -> vgic { vgicHCR = hcr })
          saveVirtTimer vcpuPtr

    vmcr <- doMachineOp get_gic_vcpu_ctrl_vmcr
    vgicUpdate vcpuPtr (\vgic -> vgic { vgicVMCR = vmcr })

    apr <- doMachineOp get_gic_vcpu_ctrl_apr
    vgicUpdate vcpuPtr (\vgic -> vgic { vgicAPR = apr })

    numListRegs <- gets (armKSGICVCPUNumListRegs . ksArchState)
    let gicIndices = init [0..numListRegs]
    mapM_ (\vreg -> do
          val <- doMachineOp $ get_gic_vcpu_ctrl_lr (fromIntegral vreg)
          vgicUpdateLR vcpuPtr (fromIntegral vreg) (fromIntegral val)) gicIndices

    armvVCPUSave vcpuPtr active

vcpuSave _ = fail "vcpuSave: no VCPU to save"

vcpuRestore :: PPtr VCPU -> Kernel ()
vcpuRestore vcpuPtr = do
    -- turn off VGIC
    doMachineOp $ set_gic_vcpu_ctrl_hcr 0
    doMachineOp $ isb

    -- restore GIC VCPU control state
    vcpu <- getObject vcpuPtr
    let vgic = vcpuVGIC vcpu

    numListRegs <- gets (armKSGICVCPUNumListRegs . ksArchState)
    let gicIndices = init [0..numListRegs]
    doMachineOp $ do
        set_gic_vcpu_ctrl_vmcr (vgicVMCR vgic)
        set_gic_vcpu_ctrl_apr (vgicAPR vgic)

        mapM_ (uncurry set_gic_vcpu_ctrl_lr) (map (\i -> (fromIntegral i, (vgicLR vgic) ! i)) gicIndices)

    -- restore banked VCPU registers except SCTLR (that's in VCPUEnable)
    vcpuRestoreRegRange vcpuPtr VCPURegTTBR0 VCPURegSPSR_EL1

    vcpuEnable vcpuPtr

vcpuInvalidateActive :: Kernel ()
vcpuInvalidateActive = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    case hsCurVCPU of
        Just (vcpuPtr, True) -> vcpuDisable Nothing
        _ -> return ()
    modifyArchState (\s -> s { armHSCurVCPU = Nothing })

vcpuSwitch :: Maybe (PPtr VCPU) -> Kernel ()
vcpuSwitch Nothing = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    case hsCurVCPU of
        Nothing -> return () -- both null, current can't be active
        Just (vcpuPtr, active) -> do -- switch to thread without vcpu
            when active $ do -- save state if not saved already
                vcpuDisable (Just vcpuPtr)
                modifyArchState (\s -> s { armHSCurVCPU = Just (vcpuPtr, False) })
            return ()
vcpuSwitch (Just new) = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    case hsCurVCPU of
        Nothing -> do -- switch to new VCPU with no current
            vcpuRestore new
            modifyArchState (\s -> s { armHSCurVCPU = Just (new, True) })
        Just (vcpuPtr, active) -> do -- switch from an existing VCPU
            if vcpuPtr /= new
                then do -- different VCPU
                    vcpuSave hsCurVCPU
                    vcpuRestore new
                    modifyArchState (\s -> s { armHSCurVCPU = Just (new, True) })
                else do -- same VCPU: switch to active
                    when (not active) $ do
                        doMachineOp isb
                        vcpuEnable new
                        modifyArchState (\s -> s { armHSCurVCPU = Just (new, True) })

{- VGICMaintenance -}

vgicMaintenance :: Kernel ()
vgicMaintenance = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    -- ignore event unless current VCPU active
    case hsCurVCPU of
        Just (vcpuPtr, True) -> do
            eisr0 <- doMachineOp $ get_gic_vcpu_ctrl_eisr0
            eisr1 <- doMachineOp $ get_gic_vcpu_ctrl_eisr1
            flags <- doMachineOp $ get_gic_vcpu_ctrl_misr
            let vgic_misr_eoi = vgicHCREN
            let irq_idx = irqIndex eisr0 eisr1

            gic_vcpu_num_list_regs <- gets (armKSGICVCPUNumListRegs . ksArchState)
            fault <-
                if (flags .&. vgic_misr_eoi /= 0)
                then
                    if (eisr0 == 0 && eisr1 == 0 ||
                        irq_idx >= gic_vcpu_num_list_regs) -- irq_idx invalid
                        then return $ VGICMaintenance Nothing
                        else (do
                            setIndex vcpuPtr irq_idx
                            return $ VGICMaintenance $ Just $ fromIntegral irq_idx
                            )
                else return $ VGICMaintenance Nothing

            curThread <- getCurThread
            runnable <- isRunnable curThread
            when runnable $ handleFault curThread $ ArchFault fault
        _ -> return ()
    where
        irqIndex eisr0 eisr1 =
            if eisr0 /= 0 then countTrailingZeros eisr0
                          else (countTrailingZeros eisr1) + 32
        setIndex vcpuPtr irq_idx = (do
                virq <- doMachineOp $ get_gic_vcpu_ctrl_lr (fromIntegral irq_idx)
                virqen <- return $ virqSetEOIIRQEN virq 0
                doMachineOp $ set_gic_vcpu_ctrl_lr (fromIntegral irq_idx) virqen
                vgicUpdateLR vcpuPtr irq_idx virqen
                )

{- VPPI Events -}

irqVPPIEventIndex :: IRQ -> Maybe VPPIEventIRQ
irqVPPIEventIndex irq =
    if irq == IRQ irqVTimerEvent then Just VPPIEventIRQ_VTimer
                                 else Nothing

vppiEvent :: IRQ -> Kernel ()
vppiEvent irq = do
    hsCurVCPU <- gets (armHSCurVCPU . ksArchState)
    case hsCurVCPU of
        Just (vcpuPtr, True) -> do
            doMachineOp $ maskInterrupt True irq
            let vppi = fromJust $ irqVPPIEventIndex irq
            vcpuUpdate vcpuPtr
                       (\vcpu -> vcpu{ vcpuVPPIMasked = vcpuVPPIMasked vcpu // [(vppi, True)] })
            curThread <- getCurThread
            runnable <- isRunnable curThread
            when runnable $ handleFault curThread $ ArchFault $ VPPIEvent irq
        _ -> return ()
