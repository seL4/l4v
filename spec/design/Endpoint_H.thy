(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Endpoint_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Endpoints"

theory Endpoint_H
imports
  EndpointDecls_H
  TCB_H
  ThreadDecls_H
  CSpaceDecls_H
  FaultHandlerDecls_H
  Notification_H
begin

defs sendIPC_def:
"sendIPC blocking call badge canGrant thread epptr\<equiv> (do
        ep \<leftarrow> getEndpoint epptr;
        (case ep of 
            IdleEP \<Rightarrow> if blocking then  (do
                setThreadState (BlockedOnSend_ \<lparr>
                    blockingObject= epptr,
                    blockingIPCBadge= badge,
                    blockingIPCCanGrant= canGrant,
                    blockingIPCIsCall= call \<rparr>) thread;
                setEndpoint epptr $ SendEP [thread]
            od)
            else  return ()
            | SendEP queue \<Rightarrow> if blocking then  (do
                setThreadState (BlockedOnSend_ \<lparr>
                    blockingObject= epptr,
                    blockingIPCBadge= badge,
                    blockingIPCCanGrant= canGrant,
                    blockingIPCIsCall= call \<rparr>) thread;
                setEndpoint epptr $ SendEP $ queue @ [thread]
            od)
            else  return ()
            | RecvEP v3 \<Rightarrow> (case v3 of dest # queue \<Rightarrow>  (do
                setEndpoint epptr $ (case queue of
                      [] \<Rightarrow>   IdleEP
                    | _ \<Rightarrow>   RecvEP queue
                    );
                recvState \<leftarrow> getThreadState dest;
                haskell_assert (isReceive recvState)
                       [];
                doIPCTransfer thread (Just epptr) badge canGrant
                    dest;
                setThreadState Running dest;
                attemptSwitchTo dest;
                fault \<leftarrow> threadGet tcbFault thread;
                (case (call, fault, canGrant) of
                      (False, None, _) \<Rightarrow>   return ()
                    | (_, _, True) \<Rightarrow>   setupCallerCap thread dest
                    | _ \<Rightarrow>   setThreadState Inactive thread
                    )
            od)
            | [] \<Rightarrow>  haskell_fail []
            )
            )
od)"

defs isActive_def:
"isActive x0\<equiv> (case x0 of
    (NTFN (ActiveNtfn _) _) \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"

defs receiveIPC_def:
"receiveIPC thread x1 isBlocking\<equiv> (let cap = x1 in
  if isEndpointCap cap
  then   (do
        epptr \<leftarrow> return ( capEPPtr cap);
        ep \<leftarrow> getEndpoint epptr;
        ntfnPtr \<leftarrow> getBoundNotification thread;
        ntfn \<leftarrow> maybe (return $ NTFN IdleNtfn Nothing) (getNotification) ntfnPtr;
        if (isJust ntfnPtr \<and> isActive ntfn)
          then completeSignal (fromJust ntfnPtr) thread
          else (case ep of
              IdleEP \<Rightarrow>   (case isBlocking of
                True \<Rightarrow>   (do
                  setThreadState (BlockedOnReceive_ \<lparr>
                      blockingObject= epptr \<rparr>) thread;
                  setEndpoint epptr $ RecvEP [thread]
                od)
              | False \<Rightarrow>   doNBRecvFailedTransfer thread
              )
            | RecvEP queue \<Rightarrow>   (case isBlocking of
                True \<Rightarrow>   (do
                  setThreadState (BlockedOnReceive_ \<lparr>
                      blockingObject= epptr \<rparr>) thread;
                  setEndpoint epptr $ RecvEP $ queue @ [thread]
                od)
              | False \<Rightarrow>   doNBRecvFailedTransfer thread
              )
            | SendEP (sender#queue) \<Rightarrow>   (do
                setEndpoint epptr $ (case queue of
                      [] \<Rightarrow>   IdleEP
                    | _ \<Rightarrow>   SendEP queue
                    );
                senderState \<leftarrow> getThreadState sender;
                haskell_assert (isSend senderState)
                       [];
                badge \<leftarrow> return ( blockingIPCBadge senderState);
                canGrant \<leftarrow> return ( blockingIPCCanGrant senderState);
                doIPCTransfer sender (Just epptr) badge canGrant
                    thread;
                call \<leftarrow> return ( blockingIPCIsCall senderState);
                fault \<leftarrow> threadGet tcbFault sender;
                (case (call, fault, canGrant) of
                      (False, None, _) \<Rightarrow>   (do
                        setThreadState Running sender;
                        switchIfRequiredTo sender
                      od)
                    | (_, _, True) \<Rightarrow>   setupCallerCap sender thread
                    | _ \<Rightarrow>   setThreadState Inactive sender
                    )
            od)
            | SendEP [] \<Rightarrow>   haskell_fail []
            )
  od)
  else   haskell_fail []
  )"

defs replyFromKernel_def:
"replyFromKernel thread x1\<equiv> (case x1 of
    (resultLabel, resultData) \<Rightarrow>    (do
    destIPCBuffer \<leftarrow> lookupIPCBuffer True thread;
    asUser thread $ setRegister badgeRegister 0;
    len \<leftarrow> setMRs thread destIPCBuffer resultData;
    msgInfo \<leftarrow> return ( MI_ \<lparr>
            msgLength= len,
            msgExtraCaps= 0,
            msgCapsUnwrapped= 0,
            msgLabel= resultLabel \<rparr>);
    setMessageInfo thread msgInfo
    od)
  )"

defs cancelIPC_def:
"cancelIPC tptr \<equiv>
        let
            replyIPCCancel = (do
                threadSet (\<lambda> tcb. tcb \<lparr>tcbFault := Nothing\<rparr>) tptr;
                slot \<leftarrow> getThreadReplySlot tptr;
                callerCap \<leftarrow> liftM (mdbNext \<circ> cteMDBNode) $ getCTE slot;
                when (callerCap \<noteq> nullPointer) $ (do
                    stateAssert (capHasProperty callerCap (\<lambda> cap. isReplyCap cap \<and>
                                                                 Not (capReplyMaster cap)))
                        [];
                    cteDeleteOne callerCap
                od)
            od);
            isIdle = (\<lambda>  ep. (case ep of
                  IdleEP \<Rightarrow>   True
                | _ \<Rightarrow>   False
                ));
            blockedIPCCancel = (\<lambda>  state. (do
                epptr \<leftarrow> return ( blockingObject state);
                ep \<leftarrow> getEndpoint epptr;
                haskell_assert (Not $ isIdle ep)
                    [];
                queue' \<leftarrow> return ( delete tptr $ epQueue ep);
                ep' \<leftarrow> (case queue' of
                      [] \<Rightarrow>   return IdleEP
                    | _ \<Rightarrow>   return $ ep \<lparr> epQueue := queue' \<rparr>
                    );
                setEndpoint epptr ep';
                setThreadState Inactive tptr
            od))
        in
                        (do
        state \<leftarrow> getThreadState tptr;
        (case state of
              BlockedOnSend _ _ _ _ \<Rightarrow>   blockedIPCCancel state
            | BlockedOnReceive _ \<Rightarrow>   blockedIPCCancel state
            | BlockedOnNotification _ \<Rightarrow>   cancelSignal tptr (waitingOnNotification state)
            | BlockedOnReply  \<Rightarrow>   replyIPCCancel
            | _ \<Rightarrow>   return ()
            )
                        od)"

defs cancelAllIPC_def:
"cancelAllIPC epptr\<equiv> (do
        ep \<leftarrow> getEndpoint epptr;
        (case ep of
              IdleEP \<Rightarrow>  
                return ()
            | _ \<Rightarrow>   (do
                setEndpoint epptr IdleEP;
                forM_x (epQueue ep) (\<lambda> t. (do
                    setThreadState Restart t;
                    tcbSchedEnqueue t
                od)
                                     );
                rescheduleRequired
            od)
            )
od)"

defs cancelBadgedSends_def:
"cancelBadgedSends epptr badge\<equiv> (do
    ep \<leftarrow> getEndpoint epptr;
    (case ep of
          IdleEP \<Rightarrow>   return ()
        | RecvEP _ \<Rightarrow>   return ()
        | SendEP queue \<Rightarrow>   (do
            setEndpoint epptr IdleEP;
            queue' \<leftarrow> (flip filterM queue) (\<lambda> t. (do
                st \<leftarrow> getThreadState t;
                if blockingIPCBadge st = badge
                    then (do
                        setThreadState Restart t;
                        tcbSchedEnqueue t;
                        return False
                    od)
                    else return True
            od));
            ep' \<leftarrow> (case queue' of
                  [] \<Rightarrow>   return IdleEP
                | _ \<Rightarrow>   return $ SendEP_ \<lparr> epQueue= queue' \<rparr>
                );
            setEndpoint epptr ep';
            rescheduleRequired
        od)
        )
od)"

defs getEndpoint_def:
"getEndpoint \<equiv> getObject"

defs setEndpoint_def:
"setEndpoint \<equiv> setObject"


end
