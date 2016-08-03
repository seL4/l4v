(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Notification_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Notifications"

theory Notification_H imports    "NotificationDecls_H"
    "TCB_H"
  TCB_H
  ThreadDecls_H
  CSpaceDecls_H
  ObjectInstances_H
begin

context begin interpretation Arch .
requalify_consts
  badgeRegister
end

defs receiveBlocked_def:
"receiveBlocked st\<equiv> (case st of
      BlockedOnReceive v2 \<Rightarrow>   True
    | _ \<Rightarrow>   False
    )"

defs sendSignal_def:
"sendSignal ntfnPtr badge\<equiv> (do
        nTFN \<leftarrow> getNotification ntfnPtr;
        (case (ntfnObj nTFN, ntfnBoundTCB nTFN) of
              (IdleNtfn, Some tcb) \<Rightarrow>   (do
                    state \<leftarrow> getThreadState tcb;
                    if (receiveBlocked state)
                      then (do
                        cancelIPC tcb;
                        setThreadState Running tcb;
                        asUser tcb $ setRegister badgeRegister badge;
                        switchIfRequiredTo tcb
                      od)
                      else
                        setNotification ntfnPtr $ nTFN \<lparr> ntfnObj := ActiveNtfn badge \<rparr>
              od)
            | (IdleNtfn, None) \<Rightarrow>   setNotification ntfnPtr $ nTFN \<lparr> ntfnObj := ActiveNtfn badge \<rparr>
            | (WaitingNtfn (dest#queue), _) \<Rightarrow>   (do
                setNotification ntfnPtr $ nTFN \<lparr>
                  ntfnObj := (case queue of
                      [] \<Rightarrow>   IdleNtfn
                    | _ \<Rightarrow>   WaitingNtfn queue
                    )
                  \<rparr>;
                setThreadState Running dest;
                asUser dest $ setRegister badgeRegister badge;
                switchIfRequiredTo dest
            od)
            | (WaitingNtfn [], _) \<Rightarrow>   haskell_fail []
            | (ActiveNtfn badge', _) \<Rightarrow>   (do
                newBadge \<leftarrow> return ( badge || badge');
                setNotification ntfnPtr $ nTFN \<lparr> ntfnObj := ActiveNtfn newBadge \<rparr>
            od)
            )
od)"

defs doNBRecvFailedTransfer_def:
"doNBRecvFailedTransfer thread \<equiv> asUser thread $ setRegister badgeRegister 0"

defs receiveSignal_def:
"receiveSignal thread cap isBlocking\<equiv> (do
        ntfnPtr \<leftarrow> return ( capNtfnPtr cap);
        ntfn \<leftarrow> getNotification ntfnPtr;
        (case ntfnObj ntfn of
              IdleNtfn \<Rightarrow>   (case isBlocking of
                  True \<Rightarrow>   (do
                      setThreadState (BlockedOnNotification_ \<lparr>
                                         waitingOnNotification= ntfnPtr \<rparr> ) thread;
                      setNotification ntfnPtr $ ntfn \<lparr>ntfnObj := WaitingNtfn ([thread]) \<rparr>
                  od)
                | False \<Rightarrow>   doNBRecvFailedTransfer thread
                )
            | WaitingNtfn queue \<Rightarrow>   (case isBlocking of
                  True \<Rightarrow>   (do
                      setThreadState (BlockedOnNotification_ \<lparr>
                                         waitingOnNotification= ntfnPtr \<rparr> ) thread;
                      setNotification ntfnPtr $ ntfn \<lparr>ntfnObj := WaitingNtfn (queue @ [thread]) \<rparr>
                  od)
                | False \<Rightarrow>   doNBRecvFailedTransfer thread
                )
            | ActiveNtfn badge \<Rightarrow>   (do
                asUser thread $ setRegister badgeRegister badge;
                setNotification ntfnPtr $ ntfn \<lparr>ntfnObj := IdleNtfn \<rparr>
            od)
            )
od)"

defs cancelAllSignals_def:
"cancelAllSignals ntfnPtr\<equiv> (do
        ntfn \<leftarrow> getNotification ntfnPtr;
        (case ntfnObj ntfn of
              WaitingNtfn queue \<Rightarrow>   (do
                setNotification ntfnPtr (ntfn \<lparr> ntfnObj := IdleNtfn \<rparr>);
                forM_x queue (\<lambda> t. (do
                    setThreadState Restart t;
                    tcbSchedEnqueue t
                od)
                                     );
                rescheduleRequired
              od)
            | _ \<Rightarrow>   return ()
            )
od)"

defs cancelSignal_def:
"cancelSignal threadPtr ntfnPtr \<equiv>
    let
      isWaiting = (\<lambda>  ntfn. (case ntfn of
                        WaitingNtfn _ \<Rightarrow>   True
                      | _ \<Rightarrow>   False
                      ))
    in
                                        (do
        ntfn \<leftarrow> getNotification ntfnPtr;
        haskell_assert (isWaiting (ntfnObj ntfn))
            [];
        queue' \<leftarrow> return ( delete threadPtr $ ntfnQueue $ ntfnObj ntfn);
        ntfn' \<leftarrow> (case queue' of
              [] \<Rightarrow>   return $ IdleNtfn
            | _ \<Rightarrow>   return $ (ntfnObj ntfn) \<lparr> ntfnQueue := queue' \<rparr>
            );
        setNotification ntfnPtr (ntfn \<lparr> ntfnObj := ntfn' \<rparr>);
        setThreadState Inactive threadPtr
                                        od)"

defs completeSignal_def:
"completeSignal ntfnPtr tcb\<equiv> (do
        ntfn \<leftarrow> getNotification ntfnPtr;
        (case ntfnObj ntfn of
              ActiveNtfn badge \<Rightarrow>   (do
                asUser tcb $ setRegister badgeRegister badge;
                setNotification ntfnPtr $ ntfn \<lparr>ntfnObj := IdleNtfn\<rparr>
              od)
            | _ \<Rightarrow>   haskell_fail []
            )
od)"

defs getNotification_def:
"getNotification \<equiv> getObject"

defs setNotification_def:
"setNotification \<equiv> setObject"

defs bindNotification_def:
"bindNotification tcb ntfnPtr\<equiv> (do
    ntfn \<leftarrow> getNotification ntfnPtr;
    setNotification ntfnPtr $ ntfn \<lparr> ntfnBoundTCB := Just tcb \<rparr>;
    setBoundNotification (Just ntfnPtr) tcb
od)"

defs doUnbindNotification_def:
"doUnbindNotification ntfnPtr ntfn tcbptr\<equiv> (do
    ntfn' \<leftarrow> return ( ntfn \<lparr> ntfnBoundTCB := Nothing \<rparr>);
    setNotification ntfnPtr ntfn';
    setBoundNotification Nothing tcbptr
od)"

defs unbindNotification_def:
"unbindNotification tcb\<equiv> (do
    ntfnPtr \<leftarrow> getBoundNotification tcb;
    (case ntfnPtr of
          Some ntfnPtr' \<Rightarrow>   (do
             ntfn \<leftarrow> getNotification ntfnPtr';
             doUnbindNotification ntfnPtr' ntfn tcb
          od)
        | None \<Rightarrow>   return ()
        )
od)"

defs unbindMaybeNotification_def:
"unbindMaybeNotification ntfnPtr\<equiv> (do
    ntfn \<leftarrow> getNotification ntfnPtr;
    (case ntfnBoundTCB ntfn of
          Some t \<Rightarrow>   doUnbindNotification ntfnPtr ntfn t
        | None \<Rightarrow>   return ()
        )
od)"


end
