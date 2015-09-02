(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

header "Threads"

theory Thread_H
imports
  ThreadDecls_H
  CSpace_H
  ArchThread_H
  FaultHandler_H
  Config_H
begin

defs configureIdleThread_def:
"configureIdleThread tcb\<equiv> (do
    ArchThreadDecls_H.configureIdleThread tcb;
    doKernelOp $ setThreadState IdleThreadState tcb
od)"

defs activateInitialThread_def:
"activateInitialThread threadPtr entry infoPtr\<equiv> (do
        asUser threadPtr $ setRegister capRegister $ fromVPtr infoPtr;
        asUser threadPtr $ setNextPC $ fromVPtr entry;
        setupReplyMaster threadPtr;
        setThreadState Running threadPtr;
        setSchedulerAction ResumeCurrentThread;
        idle \<leftarrow> getIdleThread;
        setCurThread idle;
        switchToThread threadPtr
od)"

defs activateThread_def:
"activateThread\<equiv> (do
        thread \<leftarrow> getCurThread;
        state \<leftarrow> getThreadState thread;
        (case state of
              Running \<Rightarrow>   return ()
            | Restart \<Rightarrow>   (do
                pc \<leftarrow> asUser thread $ getRestartPC;
                asUser thread $ setNextPC pc;
                setThreadState Running thread
            od)
            | IdleThreadState \<Rightarrow>   (
                ArchThreadDecls_H.activateIdleThread thread
            )
            | _ \<Rightarrow>   haskell_fail $ [] @ show state
            )
od)"

defs isBlocked_def:
"isBlocked thread\<equiv> (do
        state \<leftarrow> getThreadState thread;
        return $ (case state of
              Inactive \<Rightarrow>   True
            | BlockedOnReceive _ _ \<Rightarrow>   True
            | BlockedOnSend _ _ _ _ \<Rightarrow>   True
            | BlockedOnAsyncEvent _ \<Rightarrow>   True
            | BlockedOnReply \<Rightarrow>   True
            | _ \<Rightarrow>   False
            )
od)"

defs isRunnable_def:
"isRunnable thread\<equiv> (do
        state \<leftarrow> getThreadState thread;
        return $ (case state of
              Running \<Rightarrow>   True
            | Restart \<Rightarrow>   True
            | _ \<Rightarrow>   False
            )
od)"

defs suspend_def:
"suspend target\<equiv> (do
    ipcCancel target;
    setThreadState Inactive target;
    tcbSchedDequeue target
od)"

defs restart_def:
"restart target\<equiv> (do
    blocked \<leftarrow> isBlocked target;
    when blocked $ (do
        ipcCancel target;
        setupReplyMaster target;
        setThreadState Restart target;
        tcbSchedEnqueue target;
        switchIfRequiredTo target
    od)
od)"

defs doFaultTransfer_def:
"doFaultTransfer badge sender receiver receiverIPCBuffer\<equiv> (do
        fault \<leftarrow> threadGet tcbFault sender;
        f \<leftarrow> (case fault of
              Some f \<Rightarrow>   return f
            | None \<Rightarrow>   haskell_fail []
            );
        (faultLabel, faultMsg) \<leftarrow> makeFaultMessage f sender;
        sent \<leftarrow> setMRs receiver receiverIPCBuffer faultMsg;
        msgInfo \<leftarrow> return ( MI_ \<lparr>
             msgLength= sent,
             msgExtraCaps= 0,
             msgCapsUnwrapped= 0,
             msgLabel= faultLabel \<rparr>);
        setMessageInfo receiver msgInfo;
        asUser receiver $ setRegister badgeRegister badge
od)"

defs schedule_def:
"schedule\<equiv> (do
        curThread \<leftarrow> getCurThread;
        action \<leftarrow> getSchedulerAction;
        (case action of
              ResumeCurrentThread \<Rightarrow>   return ()
            | SwitchToThread t \<Rightarrow>   (do
                curRunnable \<leftarrow> isRunnable curThread;
                when curRunnable $ tcbSchedEnqueue curThread;
                switchToThread t;
                setSchedulerAction ResumeCurrentThread
            od)
            | ChooseNewThread \<Rightarrow>   (do
                curRunnable \<leftarrow> isRunnable curThread;
                when curRunnable $ tcbSchedEnqueue curThread;
                domainTime \<leftarrow> getDomainTime;
                when (domainTime = 0) $ nextDomain;
                chooseThread;
                setSchedulerAction ResumeCurrentThread
            od)
            )
od)"

defs chooseThread_def:
"chooseThread \<equiv>
    let
        chooseThread' = (\<lambda>  qdom prio. (do
            q \<leftarrow> getQueue qdom prio;
            (case q of
                  thread # _ \<Rightarrow>   (do
                   switchToThread thread;
                   return True
                  od)
                | [] \<Rightarrow>   return False
                )
        od))
    in
                      (do
        curdom \<leftarrow> curDomain;
        r \<leftarrow> findM (chooseThread' curdom) (reverse [0  .e.  maxPriority]);
        when (r = Nothing) $ switchToIdleThread
                      od)"

defs switchToThread_def:
"switchToThread thread\<equiv> (do
        ArchThreadDecls_H.switchToThread thread;
        tcbSchedDequeue thread;
        setCurThread thread
od)"

defs switchToIdleThread_def:
"switchToIdleThread\<equiv> (do
        thread \<leftarrow> getIdleThread;
        ArchThreadDecls_H.switchToIdleThread;
        setCurThread thread
od)"

defs setDomain_def:
"setDomain tptr newdom\<equiv> (do
        curThread \<leftarrow> getCurThread;
        tcbSchedDequeue tptr;
        threadSet (\<lambda> t. t \<lparr> tcbDomain := newdom \<rparr>) tptr;
        runnable \<leftarrow> isRunnable tptr;
        when runnable $ tcbSchedEnqueue tptr;
        when (tptr = curThread) $ rescheduleRequired
od)"

defs setPriority_def:
"setPriority tptr prio\<equiv> (do
        tcbSchedDequeue tptr;
        threadSet (\<lambda> t. t \<lparr> tcbPriority := prio \<rparr>) tptr;
        runnable \<leftarrow> isRunnable tptr;
        when runnable $ tcbSchedEnqueue tptr;
        curThread \<leftarrow> getCurThread;
        when (tptr = curThread) $ rescheduleRequired
od)"

defs possibleSwitchTo_def:
"possibleSwitchTo target onSamePriority\<equiv> (do
    curThread \<leftarrow> getCurThread;
    curDom \<leftarrow> curDomain;
    curPrio \<leftarrow> threadGet tcbPriority curThread;
    targetDom \<leftarrow> threadGet tcbDomain target;
    targetPrio \<leftarrow> threadGet tcbPriority target;
    action \<leftarrow> getSchedulerAction;
    if (targetDom \<noteq> curDom)
        then tcbSchedEnqueue target
        else (do
            if ((targetPrio > curPrio
                 \<or> (targetPrio = curPrio \<and> onSamePriority))
                \<and> action = ResumeCurrentThread)
                then setSchedulerAction $ SwitchToThread target
                else tcbSchedEnqueue target;
            (case action of
                  SwitchToThread v6 \<Rightarrow>   rescheduleRequired
                | _ \<Rightarrow>   return ()
                )
        od)
od)"

defs attemptSwitchTo_def:
"attemptSwitchTo target \<equiv> possibleSwitchTo target True"

defs switchIfRequiredTo_def:
"switchIfRequiredTo target \<equiv> possibleSwitchTo target False"

defs rescheduleRequired_def:
"rescheduleRequired\<equiv> (do
    action \<leftarrow> getSchedulerAction;
    (case action of
          SwitchToThread target \<Rightarrow>   (
            tcbSchedEnqueue target
          )
        | _ \<Rightarrow>   return ()
        );
    setSchedulerAction ChooseNewThread
od)"

defs getThreadState_def:
"getThreadState \<equiv> threadGet tcbState"

defs setThreadState_def:
"setThreadState st tptr\<equiv> (do
        threadSet (\<lambda> t. t \<lparr> tcbState := st \<rparr>) tptr;
        runnable \<leftarrow> isRunnable tptr;
        curThread \<leftarrow> getCurThread;
        action \<leftarrow> getSchedulerAction;
        when (Not runnable \<and> curThread = tptr \<and> action = ResumeCurrentThread) $
            rescheduleRequired
od)"

defs getBoundAEP_def:
"getBoundAEP \<equiv> threadGet tcbBoundAEP"

defs setBoundAEP_def:
"setBoundAEP aepptr tptr\<equiv> threadSet (\<lambda> t. t \<lparr> tcbBoundAEP := aepptr \<rparr>) tptr"

defs tcbSchedEnqueue_def:
"tcbSchedEnqueue thread\<equiv> (do
    queued \<leftarrow> threadGet tcbQueued thread;
    unless queued $ (do
        tdom \<leftarrow> threadGet tcbDomain thread;
        prio \<leftarrow> threadGet tcbPriority thread;
        queue \<leftarrow> getQueue tdom prio;
        setQueue tdom prio $ thread # queue;
        threadSet (\<lambda> t. t \<lparr> tcbQueued := True \<rparr>) thread
    od)
od)"

defs tcbSchedAppend_def:
"tcbSchedAppend thread\<equiv> (do
    queued \<leftarrow> threadGet tcbQueued thread;
    unless queued $ (do
        tdom \<leftarrow> threadGet tcbDomain thread;
        prio \<leftarrow> threadGet tcbPriority thread;
        queue \<leftarrow> getQueue tdom prio;
        setQueue tdom prio $ queue @ [thread];
        threadSet (\<lambda> t. t \<lparr> tcbQueued := True \<rparr>) thread
    od)
od)"

defs tcbSchedDequeue_def:
"tcbSchedDequeue thread\<equiv> (do
    queued \<leftarrow> threadGet tcbQueued thread;
    when queued $ (do
        tdom \<leftarrow> threadGet tcbDomain thread;
        prio \<leftarrow> threadGet tcbPriority thread;
        queue \<leftarrow> getQueue tdom prio;
        setQueue tdom prio $ filter (\<lambda>x. x \<noteq>thread) queue;
        threadSet (\<lambda> t. t \<lparr> tcbQueued := False \<rparr>) thread
    od)
od)"

defs timerTick_def:
"timerTick\<equiv> (do
  thread \<leftarrow> getCurThread;
  state \<leftarrow> getThreadState thread;
  (case state of
      Running \<Rightarrow>   (do
      ts \<leftarrow> threadGet tcbTimeSlice thread;
      ts' \<leftarrow> return ( ts - 1);
      if (ts' > 0)
        then threadSet (\<lambda> t. t \<lparr> tcbTimeSlice := ts' \<rparr>) thread
        else (do
          threadSet (\<lambda> t. t \<lparr> tcbTimeSlice := timeSlice \<rparr>) thread;
          tcbSchedAppend thread;
          rescheduleRequired
        od)
      od)
    | _ \<Rightarrow>   return ()
    );
  when (numDomains > 1) $ (do
      decDomainTime;
      domainTime \<leftarrow> getDomainTime;
      when (domainTime = 0) $ rescheduleRequired
  od)
od)"


primrec
transferCapsToSlots :: "(machine_word) option \<Rightarrow> bool \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> (capability * machine_word) list \<Rightarrow> machine_word list \<Rightarrow> message_info \<Rightarrow> message_info kernel"
where
  "transferCapsToSlots arg1 arg2 arg3 n [] arg6 mi = (
    return $ mi \<lparr> msgExtraCaps := fromIntegral n \<rparr>)"
| "transferCapsToSlots ep diminish rcvBuffer n (arg#caps) slots mi = (
    let
       transferAgain = transferCapsToSlots ep diminish rcvBuffer (n + 1) caps;
       bitN = 1 `~shiftL~` n;
       miCapUnfolded = mi \<lparr> msgCapsUnwrapped := msgCapsUnwrapped mi || bitN \<rparr>;
       (cap, srcSlot) = arg
    in
    constOnFailure (mi \<lparr> msgExtraCaps := fromIntegral n \<rparr>) $ (
        (let (v3, v4, v5) = (cap, ep, slots) in
            if isEndpointCap v3 \<and> v4 \<noteq> None \<and> capEPPtr v3 = the v4
            then let p1 = capEPPtr v3; p2 = p1
            in  (doE
                withoutFailure $
                    setExtraBadge rcvBuffer (capEPBadge cap) n;
                withoutFailure $ transferAgain slots miCapUnfolded
            odE)
            else (case v5 of
            destSlot # slots' \<Rightarrow>  (doE
                cap' \<leftarrow> unifyFailure $ deriveCap srcSlot $ if diminish
                        then allRights \<lparr> capAllowWrite := False \<rparr>
                            `~maskCapRights~` cap
                        else cap;
                whenE (isNullCap cap') $ throw undefined;
                withoutFailure $ cteInsert cap' srcSlot destSlot;
                withoutFailure $ transferAgain slots' mi
            odE)
            | _ \<Rightarrow>  returnOk $ mi \<lparr> msgExtraCaps := fromIntegral n \<rparr>
            )
            )
    ))"


defs doIPCTransfer_def:
"doIPCTransfer sender endpoint badge grant receiver diminish\<equiv> (do
        receiveBuffer \<leftarrow> lookupIPCBuffer True receiver;
        fault \<leftarrow> threadGet tcbFault sender;
        (case fault of
              None \<Rightarrow>   (do
                sendBuffer \<leftarrow> lookupIPCBuffer False sender;
                doNormalTransfer
                    sender sendBuffer endpoint badge grant
                    receiver receiveBuffer diminish
              od)
            | Some v1 \<Rightarrow>   (
                doFaultTransfer badge sender receiver receiveBuffer
            )
            )
od)"

defs doReplyTransfer_def:
"doReplyTransfer sender receiver slot\<equiv> (do
    state \<leftarrow> getThreadState receiver;
    haskell_assert (isReply state)
        [];
    mdbNode \<leftarrow> liftM cteMDBNode $ getCTE slot;
    haskell_assert (mdbPrev mdbNode \<noteq> nullPointer
                \<and> mdbNext mdbNode = nullPointer)
        [];
    parentCap \<leftarrow> getSlotCap (mdbPrev mdbNode);
    haskell_assert (isReplyCap parentCap \<and> capReplyMaster parentCap)
        [];
    fault \<leftarrow> threadGet tcbFault receiver;
    (case fault of
          None \<Rightarrow>   (do
            doIPCTransfer sender Nothing 0 True receiver False;
            cteDeleteOne slot;
            setThreadState Running receiver;
            attemptSwitchTo receiver
          od)
        | Some f \<Rightarrow>   (do
            cteDeleteOne slot;
            tag \<leftarrow> getMessageInfo sender;
            sendBuffer \<leftarrow> lookupIPCBuffer False sender;
            mrs \<leftarrow> getMRs sender sendBuffer tag;
            restart \<leftarrow> handleFaultReply f receiver (msgLabel tag) mrs;
            threadSet (\<lambda> tcb. tcb \<lparr>tcbFault := Nothing\<rparr>) receiver;
            if restart
              then (do
                setThreadState Restart receiver;
                attemptSwitchTo receiver
              od)
              else setThreadState Inactive receiver
        od)
        )
od)"

defs doNormalTransfer_def:
"doNormalTransfer sender sendBuffer endpoint badge canGrant receiver receiveBuffer diminish\<equiv> (do
        tag \<leftarrow> getMessageInfo sender;
        caps \<leftarrow> if canGrant
            then lookupExtraCaps sender sendBuffer tag
                `~catchFailure~` const (return [])
            else return [];
        msgTransferred \<leftarrow> copyMRs sender sendBuffer receiver receiveBuffer $
                                  msgLength tag;
        tag' \<leftarrow> transferCaps tag caps endpoint receiver receiveBuffer diminish;
        tag'' \<leftarrow> return ( tag' \<lparr> msgLength := msgTransferred \<rparr>);
        setMessageInfo receiver tag'';
        asUser receiver $ setRegister badgeRegister badge
od)"

defs transferCaps_def:
"transferCaps info caps endpoint receiver receiveBuffer diminish\<equiv> (do
    destSlots \<leftarrow> getReceiveSlots receiver receiveBuffer;
    info' \<leftarrow> return ( info \<lparr> msgExtraCaps := 0, msgCapsUnwrapped := 0 \<rparr>);
    (case receiveBuffer of
          None \<Rightarrow>   return info'
        | Some rcvBuffer \<Rightarrow>   (
            transferCapsToSlots endpoint diminish rcvBuffer 0
                caps destSlots info'
        )
        )
od)"


end
