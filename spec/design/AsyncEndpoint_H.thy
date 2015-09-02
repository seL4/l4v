(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Asynchronous Endpoints"

theory AsyncEndpoint_H imports    "AsyncEndpointDecls_H"
    "TCB_H"
  TCB_H
  ThreadDecls_H
  CSpaceDecls_H
  ObjectInstances_H
begin

defs receiveBlocked_def:
"receiveBlocked st\<equiv> (case st of
      BlockedOnReceive v1 v2 \<Rightarrow>   True
    | _ \<Rightarrow>   False
    )"

defs sendAsyncIPC_def:
"sendAsyncIPC aepptr badge\<equiv> (do
        aEP \<leftarrow> getAsyncEP aepptr;
        (case (aepObj aEP, aepBoundTCB aEP) of
              (IdleAEP, Some tcb) \<Rightarrow>   (do
                    state \<leftarrow> getThreadState tcb;
                    if (receiveBlocked state)
                      then (do
                        ipcCancel tcb;
                        setThreadState Running tcb;
                        asUser tcb $ setRegister badgeRegister badge;
                        switchIfRequiredTo tcb
                      od)
                      else
                        setAsyncEP aepptr $ aEP \<lparr> aepObj := ActiveAEP badge \<rparr>
              od)
            | (IdleAEP, None) \<Rightarrow>   setAsyncEP aepptr $ aEP \<lparr> aepObj := ActiveAEP badge \<rparr>
            | (WaitingAEP (dest#queue), _) \<Rightarrow>   (do
                setAsyncEP aepptr $ aEP \<lparr>
                  aepObj := (case queue of
                      [] \<Rightarrow>   IdleAEP
                    | _ \<Rightarrow>   WaitingAEP queue
                    )
                  \<rparr>;
                setThreadState Running dest;
                asUser dest $ setRegister badgeRegister badge;
                switchIfRequiredTo dest
            od)
            | (WaitingAEP [], _) \<Rightarrow>   haskell_fail []
            | (ActiveAEP badge', _) \<Rightarrow>   (do
                newBadge \<leftarrow> return ( badge || badge');
                setAsyncEP aepptr $ aEP \<lparr> aepObj := ActiveAEP newBadge \<rparr>
            od)
            )
od)"

defs receiveAsyncIPC_def:
"receiveAsyncIPC thread cap\<equiv> (do
        aepptr \<leftarrow> return ( capAEPPtr cap);
        aep \<leftarrow> getAsyncEP aepptr;
        (case aepObj aep of
              IdleAEP \<Rightarrow>   (do
                setThreadState (BlockedOnAsyncEvent_ \<lparr>
                     waitingOnAsyncEP= aepptr \<rparr> ) thread;
                setAsyncEP aepptr $ aep \<lparr>aepObj := WaitingAEP [thread] \<rparr>
              od)
            | WaitingAEP queue \<Rightarrow>   (do
                setThreadState (BlockedOnAsyncEvent_ \<lparr>
                    waitingOnAsyncEP= aepptr \<rparr> ) thread;
                setAsyncEP aepptr $ aep \<lparr>aepObj := WaitingAEP (queue @ [thread]) \<rparr>
            od)
            | ActiveAEP badge \<Rightarrow>   (do
                asUser thread $ setRegister badgeRegister badge;
                setAsyncEP aepptr $ aep \<lparr>aepObj := IdleAEP \<rparr>
            od)
            )
od)"

defs aepCancelAll_def:
"aepCancelAll aepptr\<equiv> (do
        aep \<leftarrow> getAsyncEP aepptr;
        (case aepObj aep of
              WaitingAEP queue \<Rightarrow>   (do
                setAsyncEP aepptr (aep \<lparr> aepObj := IdleAEP \<rparr>);
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

defs asyncIPCCancel_def:
"asyncIPCCancel threadPtr aepptr \<equiv>
    let
      isWaiting = (\<lambda>  aep. (case aep of
                        WaitingAEP _ \<Rightarrow>   True
                      | _ \<Rightarrow>   False
                      ))
    in
                                         (do
        aep \<leftarrow> getAsyncEP aepptr;
        haskell_assert (isWaiting (aepObj aep))
            [];
        queue' \<leftarrow> return ( delete threadPtr $ aepQueue $ aepObj aep);
        aep' \<leftarrow> (case queue' of
              [] \<Rightarrow>   return $ IdleAEP
            | _ \<Rightarrow>   return $ (aepObj aep) \<lparr> aepQueue := queue' \<rparr>
            );
        setAsyncEP aepptr (aep \<lparr> aepObj := aep' \<rparr>);
        setThreadState Inactive threadPtr
                                         od)"

defs completeAsyncIPC_def:
"completeAsyncIPC aepptr tcb\<equiv> (do
        aep \<leftarrow> getAsyncEP aepptr;
        (case aepObj aep of
              ActiveAEP badge \<Rightarrow>   (do
                asUser tcb $ setRegister badgeRegister badge;
                setAsyncEP aepptr $ aep \<lparr>aepObj := IdleAEP\<rparr>
              od)
            | _ \<Rightarrow>   haskell_fail []
            )
od)"

defs getAsyncEP_def:
"getAsyncEP \<equiv> getObject"

defs setAsyncEP_def:
"setAsyncEP \<equiv> setObject"

defs bindAsyncEndpoint_def:
"bindAsyncEndpoint tcb aepptr\<equiv> (do
    aep \<leftarrow> getAsyncEP aepptr;
    setAsyncEP aepptr $ aep \<lparr> aepBoundTCB := Just tcb \<rparr>;
    setBoundAEP (Just aepptr) tcb
od)"

defs doUnbindAEP_def:
"doUnbindAEP aepptr aep tcbptr\<equiv> (do
    aep' \<leftarrow> return ( aep \<lparr> aepBoundTCB := Nothing \<rparr>);
    setAsyncEP aepptr aep';
    setBoundAEP Nothing tcbptr
od)"

defs unbindAsyncEndpoint_def:
"unbindAsyncEndpoint tcb\<equiv> (do
    aepptr \<leftarrow> getBoundAEP tcb;
    (case aepptr of
          Some aepptr' \<Rightarrow>   (do
             aep \<leftarrow> getAsyncEP aepptr';
             doUnbindAEP aepptr' aep tcb
          od)
        | None \<Rightarrow>   return ()
        )
od)"

defs unbindMaybeAEP_def:
"unbindMaybeAEP aepptr\<equiv> (do
    aep \<leftarrow> getAsyncEP aepptr;
    (case aepBoundTCB aep of
          Some t \<Rightarrow>   doUnbindAEP aepptr aep t
        | None \<Rightarrow>   return ()
        )
od)"


end
