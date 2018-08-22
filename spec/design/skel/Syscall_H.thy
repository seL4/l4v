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

#INCLUDE_HASKELL SEL4/Model/Syscall.lhs
#INCLUDE_HASKELL SEL4/API/Syscall.lhs decls_only NOT Event Syscall
#INCLUDE_HASKELL SEL4/API/Syscall.lhs bodies_only NOT handleRecv

defs handleRecv_def:
"handleRecv isBlocking canReply\<equiv> (do
    thread \<leftarrow> getCurThread;
    epCptr \<leftarrow> getCapReg capRegister;
    ((doE
        epCap \<leftarrow> capFaultOnFailure epCptr True (lookupCap thread epCptr);
        (case epCap of
              EndpointCap _ _ _ True _ \<Rightarrow>   (doE
                replyCap \<leftarrow> if canReply then lookupReply else returnOk NullCap;
                withoutFailure $ receiveIPC thread epCap isBlocking replyCap
              odE)
            | NotificationCap ntfnPtr _ _ True \<Rightarrow>   (doE
                ntfn \<leftarrow> withoutFailure $ getNotification ntfnPtr;
                if ntfnBoundTCB ntfn = Just thread \<or> ntfnBoundTCB ntfn = Nothing
                    then withoutFailure $ receiveSignal thread epCap isBlocking
                    else throw $ CapFault epCptr True (MissingCapability 0)
            odE)
            | _ \<Rightarrow>   throw $ CapFault epCptr True (MissingCapability 0))
    odE))
      `~catchFailure~` handleFault thread
od)"

end
