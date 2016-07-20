(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Interrupt_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Interrupt_H
imports
  RetypeDecls_H
  "./$L4V_ARCH/ArchInterrupt_H"
  Notification_H
  CNode_H
  KI_Decls_H
  InterruptDecls_H
begin

context Arch begin

requalify_consts
  checkIRQ
  decodeIRQControlInvocation
  performIRQControl
  initInterruptController
  handleReservedIRQ

context begin global_naming global
requalify_consts
  InterruptDecls_H.decodeIRQControlInvocation
  InterruptDecls_H.performIRQControl
end

end

context begin interpretation Arch .

requalify_consts
  maxIRQ
  minIRQ
  maskInterrupt
  ackInterrupt
  resetTimer
  debugPrint

end

defs decodeIRQControlInvocation_def:
"decodeIRQControlInvocation label args srcSlot extraCaps \<equiv>
    (case (invocationType label, args, extraCaps) of
          (IRQIssueIRQHandler, irqW#index#depth#_, cnode#_) \<Rightarrow>   (doE
            Arch.checkIRQ (irqW && mask 16);
            irq \<leftarrow> returnOk ( toEnum (fromIntegral (irqW && mask 16)) ::irq);
            irqActive \<leftarrow> withoutFailure $ isIRQActive irq;
            whenE irqActive $ throw RevokeFirst;
            destSlot \<leftarrow> lookupTargetSlot cnode
                (CPtr index) (fromIntegral depth);
            ensureEmptySlot destSlot;
            returnOk $ IssueIRQHandler irq destSlot srcSlot
          odE)
        | (IRQIssueIRQHandler,_,_) \<Rightarrow>   throw TruncatedMessage
        | _ \<Rightarrow>   liftME ArchIRQControl $ Arch.decodeIRQControlInvocation label args srcSlot extraCaps
        )"

defs performIRQControl_def:
"performIRQControl x0\<equiv> (case x0 of
    (IssueIRQHandler irq handlerSlot controlSlot) \<Rightarrow>   
  withoutPreemption $ (do
    setIRQState (IRQSignal) irq;
    cteInsert (IRQHandlerCap irq) controlSlot handlerSlot
  od)
  | (ArchIRQControl invok) \<Rightarrow>   
    Arch.performIRQControl invok
  )"

defs decodeIRQHandlerInvocation_def:
"decodeIRQHandlerInvocation label irq extraCaps \<equiv>
    (case (invocationType label,extraCaps) of
          (IRQAckIRQ,_) \<Rightarrow>   returnOk $ AckIRQ irq
        | (IRQSetIRQHandler,(cap,slot)#_) \<Rightarrow>   (case cap of
                  NotificationCap _ _ True _ \<Rightarrow>  
                    returnOk $ SetIRQHandler irq cap slot
                | _ \<Rightarrow>   throw $ InvalidCapability 0
                )
        | (IRQSetIRQHandler,_) \<Rightarrow>   throw TruncatedMessage
        | (IRQClearIRQHandler,_) \<Rightarrow>   returnOk $ ClearIRQHandler irq
        | _ \<Rightarrow>   throw IllegalOperation
        )"

defs toBool_def:
"toBool w \<equiv> w \<noteq> 0"

defs invokeIRQHandler_def:
"invokeIRQHandler x0\<equiv> (case x0 of
    (AckIRQ irq) \<Rightarrow>   
    doMachineOp $ maskInterrupt False irq
  | (SetIRQHandler irq cap slot) \<Rightarrow>    (do
    irqSlot \<leftarrow> getIRQSlot irq;
    cteDeleteOne irqSlot;
    cteInsert cap slot irqSlot
  od)
  | (ClearIRQHandler irq) \<Rightarrow>    (do
    irqSlot \<leftarrow> getIRQSlot irq;
    cteDeleteOne irqSlot
  od)
  )"

defs deletingIRQHandler_def:
"deletingIRQHandler irq\<equiv> (do
    slot \<leftarrow> getIRQSlot irq;
    cap \<leftarrow> getSlotCap slot;
    haskell_assert (isNotificationCap cap \<or> isNullCap cap)
        [];
    cteDeleteOne slot
od)"

defs deletedIRQHandler_def:
"deletedIRQHandler irq \<equiv>
    setIRQState IRQInactive irq"

defs initInterruptController_def:
"initInterruptController rootCNCap biCapIRQC\<equiv> (doE
    frame \<leftarrow> allocFrame;
    doKernelOp $ (do
        haskell_assert (length [minBound .e. (maxBound::irq)]
               `~shiftL~` (objBits (makeObject ::cte)) \<le> bit pageBits)
            [];
        placeNewObject (ptrFromPAddr frame) (makeObject ::cte)
              (pageBits - objBits (makeObject ::cte));
        doMachineOp $ mapM_x (maskInterrupt True) [minBound  .e.  maxBound];
        irqTable \<leftarrow> return ( funArray $ const IRQInactive);
        setInterruptState $ InterruptState (ptrFromPAddr frame) irqTable;
        timerIRQ \<leftarrow> doMachineOp configureTimer;
        setIRQState IRQTimer timerIRQ;
        Arch.initInterruptController;
        slot \<leftarrow> locateSlotCap rootCNCap biCapIRQC;
        insertInitCap slot IRQControlCap
    od);
    returnOk IRQControlCap
odE)"

defs handleInterrupt_def:
"handleInterrupt irq\<equiv> (
    if (irq > maxIRQ) then doMachineOp $ ((do
         maskInterrupt True irq;
         ackInterrupt irq
    od)
                         )
     else (do
      st \<leftarrow> getIRQState irq;
      (case st of
            IRQSignal \<Rightarrow>   (do
              slot \<leftarrow> getIRQSlot irq;
              cap \<leftarrow> getSlotCap slot;
              (case cap of
                    NotificationCap _ _ True _ \<Rightarrow>  
                      sendSignal (capNtfnPtr cap) (capNtfnBadge cap)
                  | _ \<Rightarrow>   doMachineOp $ debugPrint $
                      [] @ show irq
                  );
              doMachineOp $ maskInterrupt True irq
            od)
          | IRQTimer \<Rightarrow>   (do
              timerTick;
              doMachineOp resetTimer
          od)
          | IRQReserved \<Rightarrow>   Arch.handleReservedIRQ irq
          | IRQInactive \<Rightarrow>   haskell_fail $ [] @ show irq
          );
      doMachineOp $ ackInterrupt irq
     od)
)"

defs isIRQActive_def:
"isIRQActive irq\<equiv> liftM (\<lambda>x. x \<noteq>IRQInactive) $ getIRQState irq"

defs setIRQState_def:
"setIRQState irqState irq\<equiv> (do
    st \<leftarrow> getInterruptState;
    table \<leftarrow> return ( intStateIRQTable st);
    setInterruptState $ st \<lparr> intStateIRQTable := table aLU [(irq, irqState)] \<rparr>;
    doMachineOp $ maskInterrupt (irqState=IRQInactive) irq
od)"

defs getIRQState_def:
"getIRQState irq\<equiv> liftM ((flip id irq) \<circ> intStateIRQTable) getInterruptState"

defs getIRQSlot_def:
"getIRQSlot irq\<equiv> (do
    node \<leftarrow> liftM intStateIRQNode getInterruptState;
    locateSlotBasic node (fromIntegral $ fromEnum irq)
od)"


end
