(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "System Calls"

theory Syscall_H
imports Kernel_H Event_H
begin

#INCLUDE_HASKELL SEL4/Model/Syscall.lhs
#INCLUDE_HASKELL SEL4/API/Syscall.lhs decls_only NOT Event Syscall
#INCLUDE_HASKELL SEL4/API/Syscall.lhs bodies_only NOT handleRecv

(* FIXME RT: too much internal error-monad going on for the translator to figure it out on its own. Rewrite. *)
defs handleRecv_def:
"handleRecv isBlocking canReply\<equiv> (do
    thread \<leftarrow> getCurThread;
    epCptr \<leftarrow> getCapReg capRegister;
    ((doE
        epCap \<leftarrow> capFaultOnFailure epCptr True (lookupCap thread epCptr);
        exc \<leftarrow> returnOk ( CapFault epCptr True (MissingCapability 0));
        (case epCap of
              EndpointCap _ _ _ True _ _ \<Rightarrow>   (doE
                replyCap \<leftarrow> if canReply then lookupReply else returnOk NullCap;
                withoutFailure $ receiveIPC thread epCap isBlocking replyCap
              odE)
            | NotificationCap ntfnPtr _ _ True \<Rightarrow>   (doE
                ntfn \<leftarrow> withoutFailure $ getNotification ntfnPtr;
                boundTCB \<leftarrow> returnOk $ ntfnBoundTCB ntfn;
                if boundTCB = Just thread \<or> boundTCB = Nothing
                    then withoutFailure $ receiveSignal thread epCap isBlocking
                    else throw exc
            odE)
            | _ \<Rightarrow>   throw exc)

    odE)
            )
        `~catchFailure~` handleFault thread
od)"

end
