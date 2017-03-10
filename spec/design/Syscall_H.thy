(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Syscall_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "System Calls"

theory Syscall_H
imports Kernel_H Event_H
begin

definition
syscall :: "( fault , 'a ) kernel_f \<Rightarrow> (fault \<Rightarrow> 'c kernel) \<Rightarrow> ('a \<Rightarrow> ( syscall_error , 'b ) kernel_f) \<Rightarrow> (syscall_error \<Rightarrow> 'c kernel) \<Rightarrow> ('b \<Rightarrow> 'c kernel_p) \<Rightarrow> 'c kernel_p"
where
"syscall mFault hFault mError hError mFinalise\<equiv> (doE
    rFault \<leftarrow> withoutPreemption $ runErrorT mFault;
    (case rFault of
          Inl f \<Rightarrow>   withoutPreemption $ hFault f
        | Inr a \<Rightarrow>   (doE
            rError \<leftarrow> withoutPreemption $ runErrorT $ mError a;
            (case rError of
                  Inl e \<Rightarrow>   withoutPreemption $ hError e
                | Inr b \<Rightarrow>   mFinalise b
                )
        odE)
        )
odE)"

consts'
handleEvent :: "event \<Rightarrow> unit kernel_p"

consts'
handleSend :: "bool \<Rightarrow> unit kernel_p"

consts'
handleCall :: "unit kernel_p"

consts'
handleReply :: "unit kernel"

consts'
handleRecv :: "bool \<Rightarrow> unit kernel"

consts'
handleYield :: "unit kernel"

consts'
handleInvocation :: "bool \<Rightarrow> bool \<Rightarrow> unit kernel_p"

defs handleEvent_def:
"handleEvent x0\<equiv> (case x0 of
    (SyscallEvent call) \<Rightarrow>    (case call of
          SysSend \<Rightarrow>   handleSend True
        | SysNBSend \<Rightarrow>   handleSend False
        | SysCall \<Rightarrow>   handleCall
        | SysRecv \<Rightarrow>   withoutPreemption $ handleRecv True
        | SysReply \<Rightarrow>   withoutPreemption handleReply
        | SysReplyRecv \<Rightarrow>   withoutPreemption $ (do
            handleReply;
            handleRecv True
        od)
        | SysYield \<Rightarrow>   withoutPreemption handleYield
        | SysNBRecv \<Rightarrow>   withoutPreemption $ handleRecv False
        )
  | Interrupt \<Rightarrow>    withoutPreemption $ (do
    active \<leftarrow> doMachineOp getActiveIRQ;
    (case active of
          Some irq \<Rightarrow>   handleInterrupt irq
        | None \<Rightarrow>   doMachineOp $ debugPrint []
        )
  od)
  | (UnknownSyscall n) \<Rightarrow>    withoutPreemption $ (do
    thread \<leftarrow> getCurThread;
    handleFault thread $
        UnknownSyscallException $ fromIntegral n;
    return ()
  od)
  | (UserLevelFault w1 w2) \<Rightarrow>    withoutPreemption $ (do
    thread \<leftarrow> getCurThread;
    handleFault thread $ UserException w1 (w2 && mask 29);
    return ()
  od)
  | (VMFaultEvent faultType) \<Rightarrow>    withoutPreemption $ (do
    thread \<leftarrow> getCurThread;
    handleVMFault thread faultType `~catchFailure~` handleFault thread;
    return ()
  od)
  | (HypervisorEvent hypType) \<Rightarrow>    withoutPreemption $ (do
    thread \<leftarrow> getCurThread;
    handleHypervisorFault thread hypType;
    return ()
  od)
  )"

defs handleSend_def:
"handleSend \<equiv> handleInvocation False"

defs handleCall_def:
"handleCall \<equiv> handleInvocation True True"

defs handleReply_def:
"handleReply\<equiv> (do
    thread \<leftarrow> getCurThread;
    callerSlot \<leftarrow> getThreadCallerSlot thread;
    callerCap \<leftarrow> getSlotCap callerSlot;
    (case callerCap of
          ReplyCap caller False \<Rightarrow>   (do
            haskell_assert (caller \<noteq> thread)
                [];
            doReplyTransfer thread caller callerSlot
          od)
        | NullCap \<Rightarrow>   return ()
        | _ \<Rightarrow>   haskell_fail []
        )
od)"

defs handleRecv_def:
"handleRecv isBlocking\<equiv> (do
    thread \<leftarrow> getCurThread;
    epCPtr \<leftarrow> asUser thread $ liftM CPtr $ getRegister capRegister;
    (capFaultOnFailure epCPtr True $ (doE
        epCap \<leftarrow> lookupCap thread epCPtr;
        (case epCap of
              EndpointCap _ _ _ True _ \<Rightarrow>   (
                withoutFailure $ (do
                    deleteCallerCap thread;
                    receiveIPC thread epCap isBlocking
                od)
              )
            | NotificationCap ntfnPtr _ _ True \<Rightarrow>   (doE
                ntfn \<leftarrow> withoutFailure $ getNotification ntfnPtr;
                boundTCB \<leftarrow> returnOk $ ntfnBoundTCB ntfn;
                if boundTCB = Just thread \<or> boundTCB = Nothing
                 then withoutFailure $ receiveSignal thread epCap isBlocking
                 else throw $ MissingCapability_ \<lparr> missingCapBitsLeft= 0 \<rparr>
            odE)
            | _ \<Rightarrow>   throw $ MissingCapability_ \<lparr> missingCapBitsLeft= 0 \<rparr>)
            
    odE)
            )
      `~catchFailure~` handleFault thread;
    return ()
od)"

defs handleYield_def:
"handleYield\<equiv> (do
    thread \<leftarrow> getCurThread;
    tcbSchedDequeue thread;
    tcbSchedAppend thread;
    rescheduleRequired
od)"

defs handleInvocation_def:
"handleInvocation isCall isBlocking\<equiv> (doE
    thread \<leftarrow> withoutPreemption getCurThread;
    info \<leftarrow> withoutPreemption $ getMessageInfo thread;
    ptr \<leftarrow> withoutPreemption $ asUser thread $ liftM CPtr $
        getRegister capRegister;
    syscall
        ((doE
            (cap, slot) \<leftarrow> capFaultOnFailure ptr False $ lookupCapAndSlot thread ptr;
            buffer \<leftarrow> withoutFailure $ lookupIPCBuffer False thread;
            extracaps \<leftarrow> lookupExtraCaps thread buffer info;
            returnOk (slot, cap, extracaps, buffer)
        odE)
                                                   )
        (\<lambda> fault.
            when isBlocking $ handleFault thread fault)
        (\<lambda> (slot, cap, extracaps, buffer). (doE
            args \<leftarrow> withoutFailure $ getMRs thread buffer info;
            decodeInvocation (msgLabel info) args ptr slot cap extracaps
        odE)
                                                                        )
        (\<lambda> err. when isCall $
            replyFromKernel thread $ msgFromSyscallError err)
        (\<lambda> oper. (doE
            withoutPreemption $ setThreadState Restart thread;
            reply \<leftarrow> performInvocation isBlocking isCall oper;
            withoutPreemption $ (do
                state \<leftarrow> getThreadState thread;
                (case state of
                      Restart \<Rightarrow>   (do
                        when isCall $ replyFromKernel thread (0, reply);
                        setThreadState Running thread
                      od)
                    | _ \<Rightarrow>   return ())
                    
            od)
                    
        odE)
                    )
odE)"


end
