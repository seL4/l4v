(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file Delete_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Deleting Capabilities"

theory Delete_H
imports
  CNode_H
  Interrupt_H
  Endpoint_H
  Thread_H
begin

definition
  slotsPointed :: "capability \<Rightarrow> machine_word set"
where
 "slotsPointed cap \<equiv> case cap of
   CNodeCap ptr a b c   \<Rightarrow> {ptr}
 | ThreadCap ptr        \<Rightarrow> {ptr}
 | Zombie ptr bits num  \<Rightarrow> {ptr}
 | _                    \<Rightarrow> {}"

primrec
  sethelper :: "bool \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "sethelper True  s = {}"
| "sethelper False s = s"

function
  finaliseSlot' :: "machine_word \<Rightarrow> bool \<Rightarrow> (bool * irq option) kernel_p"
where
 "finaliseSlot' x b s =
(\<lambda> finaliseSlot.
(\<lambda> cteDelete.
(\<lambda> reduceZombie.
(\<lambda>slot exposed.  (doE
    cte \<leftarrow> withoutPreemption $ getCTE slot;
    if isNullCap $ cteCap cte then returnOk (True, Nothing) else (doE
        final \<leftarrow> withoutPreemption $ isFinalCapability cte;
        (remainder, irq) \<leftarrow> withoutPreemption $
                                finaliseCap (cteCap cte) final False;
        if capRemovable remainder slot then returnOk (True, irq) else
            if Not exposed \<and> capCyclicZombie remainder slot
            then (doE
                withoutPreemption $ updateCap slot remainder;
                returnOk (False, Nothing)
            odE)
            else (doE
                withoutPreemption $ updateCap slot remainder;
                reduceZombie remainder slot exposed;
                preemptionPoint;
                finaliseSlot slot exposed
            odE)
    odE)
odE))

)
(
(\<lambda>x0 slot x2.  (let (v33, v34) = (x0, x2) in
  if isZombie v33 \<and> capZombieNumber v33 = 0
  then  
    haskell_fail []
  else if isZombie v33 \<and> \<not> v34
  then let ptr = capZombiePtr v33
  in   (doE
    haskell_assertE (ptr \<noteq> slot) [];
    capAtPtr \<leftarrow> withoutPreemption $ liftM cteCap $ getCTE ptr;
    (case capAtPtr of
          (Zombie ptr2 _ _) \<Rightarrow>   haskell_assertE (ptr2 \<noteq> ptr)
                []
        | _ \<Rightarrow>   returnOk ()
        );
    withoutPreemption $ capSwapForDelete ptr slot
  odE)
  else if isZombie v33 \<and> v34
  then let z = v33; ptr = capZombiePtr z; n = capZombieNumber z
  in   (doE
    endSlot \<leftarrow> withoutPreemption $ locateSlotCap z (fromIntegral (n - 1));
    cteDelete endSlot False;
    ourCTE  \<leftarrow> withoutPreemption $ getCTE slot;
    (let c2 = (cteCap ourCTE) in
        if isNullCap c2
        then  returnOk ()
        else if isZombie c2
        then let ptr2 = capZombiePtr c2
        in 
            if (ptr = ptr2 \<and> capZombieNumber c2 = n
                    \<and> capZombieType z = capZombieType c2)
            then withoutPreemption $ (do
                endCTE \<leftarrow> getCTE endSlot;
                haskell_assert (isNullCap $ cteCap endCTE)
                    [];
                newCap \<leftarrow> return ( z \<lparr> capZombieNumber := n- 1 \<rparr>);
                updateCap slot newCap
            od)
            else haskell_assertE (ptr2 = slot \<and> ptr \<noteq> slot)
                    []
        else  haskell_fail []
        )
  odE)
  else   haskell_fail []
  ))

)
)
(
(\<lambda>slot exposed.  (doE
    (success, irq) \<leftarrow> finaliseSlot slot exposed;
    whenE (exposed \<or> success) $ withoutPreemption $ emptySlot slot irq
odE))

)
)
finaliseSlot' x b s"

  by auto

defs
  finaliseSlot_def:
 "finaliseSlot \<equiv> finaliseSlot'"


function
  cteDeleteOne' :: "machine_word \<Rightarrow> unit kernel"
where
 "cteDeleteOne' x s =
(\<lambda> cteDeleteOne.
(\<lambda> deletingIRQHandler.
(\<lambda> cancelIPC.
(\<lambda> suspend.
(\<lambda> finaliseCap.
(\<lambda>slot.  (do
    cte \<leftarrow> getCTE slot;
    unless (isNullCap $ cteCap cte) $ (do
        final \<leftarrow> isFinalCapability cte;
        (remainder, irq) \<leftarrow> finaliseCap (cteCap cte) final True;
        haskell_assert (capRemovable remainder slot \<and> irq = Nothing) $
            [];
        emptySlot slot Nothing
    od)
od))

)
(
(\<lambda>x0 x1 x2.  (let (v1, v2, v3) = (x0, x1, x2) in
  if isEndpointCap v1
  then let ptr = capEPPtr v1; final = v2
  in   (do
    when final $ cancelAllIPC ptr;
    return (NullCap, Nothing)
  od)
  else if isNotificationCap v1
  then let ptr = capNtfnPtr v1; final = v2
  in   (do
    when final $ (do
        unbindMaybeNotification ptr;
        cancelAllSignals ptr
    od);
    return (NullCap, Nothing)
  od)
  else if isReplyCap v1
  then   return (NullCap, Nothing)
  else if isNullCap v1
  then   return (NullCap, Nothing)
  else if isDomainCap v1
  then   return (NullCap, Nothing)
  else if v3
  then   haskell_fail []
  else if isCNodeCap v1 \<and> v2
  then let ptr = capCNodePtr v1; bits = capCNodeBits v1
  in  
    return (Zombie ptr (ZombieCNode bits) (bit bits), Nothing)
  else if isThreadCap v1 \<and> v2
  then let tcb = capTCBPtr v1
  in   (do
    cte_ptr \<leftarrow> getThreadCSpaceRoot tcb;
    unbindNotification tcb;
    suspend tcb;
    Arch.prepareThreadDelete tcb;
    return (Zombie cte_ptr ZombieTCB 5, Nothing)
  od)
  else if isZombie v1 \<and> v2
  then let z = v1
  in  
    return (z, Nothing)
  else if isArchObjectCap v1
  then let cap = capCap v1; final = v2
  in  
    liftM (\<lambda> cap. (cap, Nothing)) $ Arch.finaliseCap cap final
  else if isIRQHandlerCap v1 \<and> v2
  then let irq = capIRQ v1
  in   (do
    deletingIRQHandler irq;
    return (NullCap, Just irq)
  od)
  else if isZombie v1 \<and> \<not> v2
  then   haskell_fail []
  else   return (NullCap, Nothing)
  ))

)
)
(
(\<lambda>target.  (do
    cancelIPC target;
    setThreadState Inactive target;
    tcbSchedDequeue target
od))

)
)
(
(\<lambda>tptr. 
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
                        od))

)
)
(
(\<lambda>irq.  (do
    slot \<leftarrow> getIRQSlot irq;
    cap \<leftarrow> getSlotCap slot;
    haskell_assert (isNotificationCap cap \<or> isNullCap cap)
        [];
    cteDeleteOne slot
od))

)
)
cteDeleteOne' x s"

  by auto

defs
  cteDeleteOne_def1:
 "cteDeleteOne \<equiv> cteDeleteOne'"

termination cteDeleteOne'
  by (rule cteDeleteOne'.termination[OF wf_empty], simp+)

lemma cteDeleteOne_def:
 "cteDeleteOne =
(
(\<lambda>slot.  (do
    cte \<leftarrow> getCTE slot;
    unless (isNullCap $ cteCap cte) $ (do
        final \<leftarrow> isFinalCapability cte;
        (remainder, irq) \<leftarrow> finaliseCap (cteCap cte) final True;
        haskell_assert (capRemovable remainder slot \<and> irq = Nothing) $
            [];
        emptySlot slot Nothing
    od)
od))

)"
  apply (rule ext)+
  apply (subst cteDeleteOne_def1)
  apply (subst cteDeleteOne'.simps)
  apply (unfold finaliseCap_def suspend_def cancelIPC_def
                deletingIRQHandler_def cteDeleteOne_def1)
  apply (rule refl)
  done

lemma card_reduce:
  "(s :: ('a :: finite) set) \<inter> s' = {} \<Longrightarrow> card (UNIV - (s \<union> s')) < card (UNIV - s) = (s' \<noteq> {})"
  apply (case_tac "s' \<subseteq> s")
   apply (simp add: Un_absorb2)
   apply (simp add: Int_absorb1)
  apply (clarsimp simp: subset_iff)
  apply (subst psubset_card_mono)
    apply simp
   apply blast
  apply blast
  done

lemma isCapDs:
  "isUntypedCap cap \<Longrightarrow> \<exists>dev ptr size freeIndex. cap = UntypedCap dev ptr size freeIndex"
  "isEndpointCap cap \<Longrightarrow> \<exists>ptr bdg cans canr cang. cap = EndpointCap ptr bdg cans canr cang"
  "isNotificationCap cap \<Longrightarrow> \<exists>ptr bdg cans canr. cap = NotificationCap ptr bdg cans canr"
  "isCNodeCap cap \<Longrightarrow> \<exists>ptr bits grd gsize. cap = CNodeCap ptr bits grd gsize"
  "isThreadCap cap \<Longrightarrow> \<exists>ptr. cap = ThreadCap ptr"
  "isArchObjectCap cap \<Longrightarrow> \<exists>archcap. cap = ArchObjectCap archcap"
  "isZombie cap \<Longrightarrow> \<exists>ptr bits num. cap = Zombie ptr bits num"
  apply (case_tac cap, simp_all add: isUntypedCap_def)
  apply (case_tac cap, simp_all add: isEndpointCap_def)
  apply (case_tac cap, simp_all add: isNotificationCap_def)
  apply (case_tac cap, simp_all add: isCNodeCap_def)
  apply (case_tac cap, simp_all add: isThreadCap_def)
  apply (case_tac cap, simp_all add: isArchObjectCap_def)
  apply (case_tac cap, simp_all add: isZombie_def)
  done

end
