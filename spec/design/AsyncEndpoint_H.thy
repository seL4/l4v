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

theory AsyncEndpoint_H
imports
  TCB_H
  ThreadDecls_H
  CSpaceDecls_H
  ObjectInstances_H
begin

consts
sendAsyncIPC :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
receiveAsyncIPC :: "machine_word \<Rightarrow> capability \<Rightarrow> unit kernel"

consts
aepCancelAll :: "machine_word \<Rightarrow> unit kernel"

consts
asyncIPCCancel :: "machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"

consts
getAsyncEP :: "machine_word \<Rightarrow> async_endpoint kernel"

consts
setAsyncEP :: "machine_word \<Rightarrow> async_endpoint \<Rightarrow> unit kernel"

defs sendAsyncIPC_def:
"sendAsyncIPC aepptr badge val\<equiv> (do
        aEP \<leftarrow> getAsyncEP aepptr;
        (case aEP of
              IdleAEP \<Rightarrow>   (
                setAsyncEP aepptr $ ActiveAEP badge val
              )
            | WaitingAEP (dest#queue) \<Rightarrow>   (do
                setAsyncEP aepptr $ (case queue of
                      [] \<Rightarrow>   IdleAEP
                    | _ \<Rightarrow>   WaitingAEP queue
                    );
                setThreadState Running dest;
                doAsyncTransfer badge val dest;
                switchIfRequiredTo dest
            od)
            | WaitingAEP [] \<Rightarrow>   haskell_fail []
            | ActiveAEP badge' val' \<Rightarrow>   (do
                newVal   \<leftarrow> return ( val || val');
                newBadge \<leftarrow> return ( badge || badge');
                setAsyncEP aepptr $ ActiveAEP newBadge newVal
            od)
            )
od)"

defs receiveAsyncIPC_def:
"receiveAsyncIPC thread cap\<equiv> (do
        aepptr \<leftarrow> return ( capAEPPtr cap);
        aep \<leftarrow> getAsyncEP aepptr;
        (case aep of
              IdleAEP \<Rightarrow>   (do
                setThreadState (BlockedOnAsyncEvent_ \<lparr>
                     waitingOnAsyncEP= aepptr \<rparr> ) thread;
                setAsyncEP aepptr $ WaitingAEP [thread]
              od)
            | WaitingAEP queue \<Rightarrow>   (do
                setThreadState (BlockedOnAsyncEvent_ \<lparr>
                    waitingOnAsyncEP= aepptr \<rparr> ) thread;
                setAsyncEP aepptr $ WaitingAEP $ queue @ [thread]
            od)
            | ActiveAEP badge currentValue \<Rightarrow>   (do
                doAsyncTransfer badge currentValue thread;
                setAsyncEP aepptr $ IdleAEP
            od)
            )
od)"

defs aepCancelAll_def:
"aepCancelAll aepptr\<equiv> (do
        aep \<leftarrow> getAsyncEP aepptr;
        (case aep of
              WaitingAEP queue \<Rightarrow>   (do
                setAsyncEP aepptr IdleAEP;
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
        haskell_assert (isWaiting aep)
            [];
        queue' \<leftarrow> return ( delete threadPtr $ aepQueue aep);
        aep' \<leftarrow> (case queue' of
              [] \<Rightarrow>   return IdleAEP
            | _ \<Rightarrow>   return $ aep \<lparr> aepQueue := queue' \<rparr>
            );
        setAsyncEP aepptr aep';
        setThreadState Inactive threadPtr
                                         od)"

defs getAsyncEP_def:
"getAsyncEP \<equiv> getObject"

defs setAsyncEP_def:
"setAsyncEP \<equiv> setObject"


end
