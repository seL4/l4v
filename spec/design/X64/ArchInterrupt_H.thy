(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchInterrupt_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchInterrupt_H
imports "../RetypeDecls_H" "../CNode_H" "../InterruptDecls_H" ArchInterruptDecls_H
begin

context Arch begin global_naming X64_H

defs decodeIRQControlInvocation_def:
"decodeIRQControlInvocation label args srcSlot extraCaps \<equiv>
    (let (label, args, extraCaps) = (invocationType label, args, extraCaps) in
        case (label, args, extraCaps) of
        (ArchInvocationLabel X64IRQIssueIRQHandlerIOAPIC,
        index#depth#ioapic#pin#level#polarity#irqW#_, cnode#_) =>  (doE
            rangeCheck irqW (fromEnum minIRQ) (fromEnum maxIRQ);
            irq \<leftarrow> returnOk ( toEnum (fromIntegral irqW) ::irq);
            destSlot \<leftarrow> lookupTargetSlot cnode (CPtr index)
                (fromIntegral depth);
            ensureEmptySlot destSlot;
            rangeCheck ioapic 0 (numIOAPICs - 1);
            rangeCheck pin 0 (ioapicIRQLines - 1);
            rangeCheck level (0::machine_word) 1;
            rangeCheck polarity (0::machine_word) 1;
            vector \<leftarrow> returnOk ( (fromIntegral $ fromEnum irq) + irqIntOffset);
            returnOk $ IssueIRQHandlerIOAPIC irq destSlot srcSlot ioapic
                pin level polarity vector
        odE)
        | (ArchInvocationLabel X64IRQIssueIRQHandlerMSI,
        index#depth#pciBus#pciDev#pciFunc#handle#irqW#_, cnode#_) =>  (doE
            rangeCheck irqW (fromEnum minIRQ) (fromEnum maxIRQ);
            irq \<leftarrow> returnOk ( toEnum (fromIntegral irqW) ::irq);
            destSlot \<leftarrow> lookupTargetSlot cnode (CPtr index)
                (fromIntegral depth);
            ensureEmptySlot destSlot;
            rangeCheck pciBus 0 maxPCIBus;
            rangeCheck pciDev 0 maxPCIDev;
            rangeCheck pciFunc 0 maxPCIFunc;
            returnOk $ IssueIRQHandlerMSI irq destSlot srcSlot pciBus
                pciDev pciFunc handle
        odE)
        | _ =>  throw IllegalOperation
        )"

defs performIRQControl_def:
"performIRQControl x0\<equiv> (let inv = x0 in
  case inv of
  (IssueIRQHandlerIOAPIC irq destSlot srcSlot ioapic pin level polarity vector) =>   withoutPreemption $ (do
    doMachineOp $ ioapicMapPinToVector ioapic pin level polarity vector;
    irqState \<leftarrow> return $ IRQIOAPIC ioapic pin level polarity True;
    doMachineOp $ updateIRQState irq irqState;
    setIRQState IRQSignal (IRQ irq);
    cteInsert (IRQHandlerCap (IRQ irq)) destSlot srcSlot;
    return ()
  od)
  | (IssueIRQHandlerMSI irq destSlot srcSlot pciBus pciDev pciFunc handle) =>   withoutPreemption $ (do
    irqState \<leftarrow> return $ IRQMSI pciBus pciDev pciFunc handle;
    doMachineOp $ updateIRQState irq irqState;
    setIRQState IRQSignal (IRQ irq);
    cteInsert (IRQHandlerCap (IRQ irq)) destSlot srcSlot;
    return ()
  od)
  )"

defs checkIRQ_def:
"checkIRQ irq\<equiv> rangeCheck irq (fromEnum minIRQ) (fromEnum maxIRQ)"

defs handleReservedIRQ_def:
"handleReservedIRQ arg1 \<equiv> return ()"

defs initInterruptController_def:
"initInterruptController\<equiv> return ()"


end

end
