%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module specifies the contents and behaviour of a synchronous IPC endpoint.

> module SEL4.Object.Endpoint (
>         sendIPC, receiveIPC,
>         cancelIPC, cancelAllIPC, cancelBadgedSends, epBlocked, reorderEp
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: cancelIPC #-}

> import Prelude hiding (Word)
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Reply(updateReply, getReply, replyPush, replyRemove, replyUnlink, replyRemoveTCB)
> import SEL4.Object.SchedContext
> import SEL4.Object.Structures
> import SEL4.Object.Instances()
> import SEL4.Object.Notification
> import {-# SOURCE #-} SEL4.Object.CNode
> import {-# SOURCE #-} SEL4.Object.TCB
> import {-# SOURCE #-} SEL4.Kernel.Thread
> import {-# SOURCE #-} SEL4.Kernel.VSpace

> import Data.List
> import Data.Maybe
> import Data.Helpers (mapMaybe, distinct)

\end{impdetails}

\subsection{Sending IPC}

This function performs an IPC send operation, given a pointer to the sending thread, a capability to an endpoint, and possibly a fault that should be sent instead of a message from the thread.

> sendIPC :: Bool -> Bool -> Word -> Bool -> Bool -> Bool -> PPtr TCB ->
>         PPtr Endpoint -> Kernel ()

The normal (blocking) version of the send operation will remove a recipient from the endpoint's queue if one is available, or otherwise add the sender to the queue.

> sendIPC blocking call badge canGrant canGrantReply canDonate thread epptr = do
>         stateAssert sym_refs_asrt
>             "Assert that `sym_refs (state_refs_of' s)` holds"
>         stateAssert valid_idle'_asrt
>             "Assert that `valid_idle' s` holds"
>         ep <- getEndpoint epptr
>         case ep of

If the endpoint is idle, and this is a blocking IPC operation, then the current thread is queued in the endpoint, which changes to the sending state. The thread will block until a receive operation is performed on the endpoint.

>             IdleEP | blocking -> do
>                 setThreadState (BlockedOnSend {
>                     blockingObject = epptr,
>                     blockingIPCBadge = badge,
>                     blockingIPCCanGrant = canGrant,
>                     blockingIPCCanGrantReply = canGrantReply,
>                     blockingIPCIsCall = call }) thread
>                 setEndpoint epptr $ SendEP [thread]

If the endpoint is already in the sending state, and this is a blocking IPC operation, then the current thread is blocked and added to the queue.

>             SendEP queue | blocking -> do
>                 setThreadState (BlockedOnSend {
>                     blockingObject = epptr,
>                     blockingIPCBadge = badge,
>                     blockingIPCCanGrant = canGrant,
>                     blockingIPCCanGrantReply = canGrantReply,
>                     blockingIPCIsCall = call }) thread
>                 qs' <- tcbEPAppend thread queue
>                 setEndpoint epptr $ SendEP qs'

A non-blocking IPC to an idle or sending endpoint will be silently dropped.

>             IdleEP -> return ()
>             SendEP _ -> return ()

If the endpoint is receiving, then a thread is removed from its queue, and an IPC transfer is performed. If the recipient is the last thread in the endpoint's queue, the endpoint becomes idle.

>             RecvEP (dest:queue) -> do
>                 setEndpoint epptr $ case queue of
>                     [] -> IdleEP
>                     _ -> RecvEP queue
>                 recvState <- getThreadState dest
>                 assert (isReceive recvState)
>                        "TCB in receive endpoint queue must be blocked on receive"
>                 doIPCTransfer thread (Just epptr) badge canGrant dest
>                 let replyOpt = replyObject recvState
>                 case replyOpt of
>                     Just reply -> replyUnlink reply dest
>                     _ -> return ()
>                 scOptDest <- threadGet tcbSchedContext dest
>                 fault <- threadGet tcbFault thread
>                 if (call || isJust fault)
>                   then if ((canGrant || canGrantReply) && isJust replyOpt)
>                     then replyPush thread dest (fromJust replyOpt) canDonate
>                     else setThreadState Inactive thread
>                   else when (canDonate && scOptDest == Nothing) $ do
>                     scOptSrc <- threadGet tcbSchedContext thread
>                     schedContextDonate (fromJust scOptSrc) dest


The receiving thread has now completed its blocking operation and can run. If the receiving thread has higher priority than the current thread, the scheduler is instructed to switch to it immediately.

>                 setThreadState Running dest
>                 scOpt <- threadGet tcbSchedContext dest
>                 ifCondRefillUnblockCheck scOpt (Just False) (Just False)
>                 possibleSwitchTo dest

Empty receive endpoints are invalid.

>             RecvEP [] -> fail "Receive endpoint queue must not be empty"

\subsection{Receiving IPC}

The IPC receive operation is essentially the same as the send operation, but with the send and receive states swapped. There are a few other differences: the badge must be retrieved from the TCB when completing an operation, and is not set when adding a TCB to the queue; also, the operation always blocks if no partner is immediately available; lastly, the receivers thread state does not need updating to Running however the senders state may.

> isActive :: Notification -> Bool
> isActive (NTFN (ActiveNtfn _) _ _) = True
> isActive _ = False

> isTimeoutFault :: Fault -> Bool
> isTimeoutFault (Timeout _) = True
> isTimeoutFault _ = False

> receiveIPC :: PPtr TCB -> Capability -> Bool -> Capability -> Kernel ()
> receiveIPC thread cap@(EndpointCap {}) isBlocking replyCap = do
>         let epptr = capEPPtr cap
>         stateAssert sym_refs_asrt
>             "Assert that `sym_refs (state_refs_of' s)` holds"
>         stateAssert sch_act_wf_asrt
>             "Assert that `sch_act_wf (ksSchedulerAction s) s` holds"
>         stateAssert valid_idle'_asrt
>             "Assert that `valid_idle' s` holds"
>         replyOpt <- (case replyCap of
>             ReplyCap r _ -> return (Just r)
>             NullCap -> return Nothing
>             _ -> fail "receiveIPC: replyCap must be ReplyCap or NullCap")
>         when (replyOpt /= Nothing) $ do
>             tptrOpt <- liftM replyTCB (getReply (fromJust replyOpt))
>             when (tptrOpt /= Nothing && tptrOpt /= Just thread) $ do
>                 cancelIPC $ fromJust tptrOpt
>         let recvCanGrant = capEPCanGrant cap
>         ep <- getEndpoint epptr
>         -- check if anything is waiting on bound ntfn
>         ntfnPtr <- getBoundNotification thread
>         ntfn <- maybe (return $ NTFN IdleNtfn Nothing Nothing) getNotification ntfnPtr
>         if (isJust ntfnPtr && isActive ntfn)
>           then completeSignal (fromJust ntfnPtr) thread
>           else do
>             when (ntfnPtr /= Nothing && isBlocking) $
>               maybeReturnSc (fromJust ntfnPtr) thread
>             case ep of
>               IdleEP -> case isBlocking of
>                 True -> do
>                     setThreadState (BlockedOnReceive {
>                         blockingObject = epptr,
>                         blockingIPCCanGrant = recvCanGrant,
>                         replyObject = replyOpt }) thread
>                     when (replyOpt /= Nothing) $
>                         updateReply (fromJust replyOpt) (\reply -> reply { replyTCB = Just thread })
>                     setEndpoint epptr $ RecvEP [thread]
>                 False -> doNBRecvFailedTransfer thread
>               RecvEP queue -> case isBlocking of
>                 True -> do
>                     setThreadState (BlockedOnReceive {
>                         blockingObject = epptr,
>                         blockingIPCCanGrant = recvCanGrant,
>                         replyObject = replyOpt}) thread
>                     when (replyOpt /= Nothing) $
>                         updateReply (fromJust replyOpt) (\reply -> reply { replyTCB = Just thread })
>                     qs' <- tcbEPAppend thread queue
>                     setEndpoint epptr $ RecvEP $ qs'
>                 False -> doNBRecvFailedTransfer thread
>               SendEP (sender:queue) -> do
>                   setEndpoint epptr $ case queue of
>                       [] -> IdleEP
>                       _ -> SendEP queue
>                   senderState <- getThreadState sender
>                   assert (isSend senderState)
>                          "TCB in send endpoint queue must be blocked on send"
>                   let badge = blockingIPCBadge senderState
>                   let canGrant = blockingIPCCanGrant senderState
>                   let canGrantReply = blockingIPCCanGrantReply senderState
>                   doIPCTransfer sender (Just epptr) badge canGrant thread
>                   scOpt <- threadGet tcbSchedContext sender
>                   ifCondRefillUnblockCheck scOpt (Just False) (Just True)
>                   let call = blockingIPCIsCall senderState
>                   fault <- threadGet tcbFault sender
>                   if (call || isJust fault)
>                       then if ((canGrant || canGrantReply) && replyOpt /= Nothing)
>                           then do
>                               senderSc <- threadGet tcbSchedContext sender
>                               donate <- return ((senderSc /= Nothing) && not (isJust fault && isTimeoutFault (fromJust fault)))
>                               replyPush sender thread (fromJust replyOpt) donate
>                           else setThreadState Inactive sender
>                       else do
>                           setThreadState Running sender
>                           possibleSwitchTo sender
>               SendEP [] -> fail "Send endpoint queue must not be empty"

> receiveIPC _ _ _ _ = fail "receiveIPC: invalid cap"

\subsection{Cancelling IPC}

If a thread is waiting for an IPC operation, it may be necessary to move the thread into a state where it is no longer waiting; for example if the thread is deleted. The following function, given a pointer to a thread, cancels any IPC that thread is involved in.

> cancelIPC :: PPtr TCB -> Kernel ()
> cancelIPC tptr = do
>         stateAssert sym_refs_asrt
>             "Assert that `sym_refs (state_refs_of' s)` holds"
>         stateAssert ready_qs_runnable
>             "Threads in the ready queues are runnable'"
>         state <- getThreadState tptr
>         threadSet (\tcb -> tcb {tcbFault = Nothing}) tptr
>         case state of

Threads blocked waiting for endpoints will simply be removed from the endpoint queue.

>             BlockedOnSend {} -> blockedCancelIPC state tptr Nothing
>             BlockedOnReceive _ _ replyOpt -> blockedCancelIPC state tptr replyOpt
>             BlockedOnNotification {} -> cancelSignal tptr (waitingOnNotification state)

Threads that are waiting for an ipc reply or a fault response must have their reply capability revoked.

>             BlockedOnReply {} -> replyRemoveTCB tptr
>             _ -> return ()

If a thread is blocking on an endpoint, then the endpoint is fetched and the thread removed from its queue.

> blockedCancelIPC :: ThreadState -> PPtr TCB -> Maybe (PPtr Reply) -> Kernel ()
> blockedCancelIPC state tptr replyOpt = do
>     epptr <- getBlockingObject state
>     ep <- getEndpoint epptr
>     assert (not $ isIdle ep)
>         "blockedCancelIPC: endpoint must not be idle"
>     assert (distinct (epQueue ep)) "the endpoint queue of ep must be a list of distinct pointers"
>     let queue' = delete tptr $ epQueue ep
>     ep' <- return $ case queue' of
>         [] -> IdleEP
>         _ -> ep { epQueue = queue' }
>     setEndpoint epptr ep'
>     case replyOpt of
>         Nothing -> return ()
>         Just reply -> replyUnlink reply tptr

Finally, replace the IPC block with a fault block (which will retry the operation if the thread is resumed).

>     setThreadState Inactive tptr
>
>     where
>         isIdle ep = case ep of
>             IdleEP -> True
>             _      -> False

> restartThreadIfNoFault :: PPtr TCB -> Kernel ()
> restartThreadIfNoFault t = do
>         fault <- threadGet tcbFault t
>         if isNothing fault
>             then do
>                 setThreadState Restart t
>                 scOpt <- threadGet tcbSchedContext t
>                 ifCondRefillUnblockCheck scOpt (Just False) (Just True)
>                 possibleSwitchTo t
>             else setThreadState Inactive t

> cancelAllIPC_loop_body :: PPtr TCB -> Kernel ()
> cancelAllIPC_loop_body t = do
>         st <- getThreadState t
>         let replyOpt = if isReceive st then replyObject st else Nothing
>         case replyOpt of
>             Nothing -> return ()
>             Just reply -> replyUnlink reply t
>         restartThreadIfNoFault t

If an endpoint is deleted, then every pending IPC operation using it must be cancelled.

> cancelAllIPC :: PPtr Endpoint -> Kernel ()
> cancelAllIPC epptr = do
>         stateAssert sym_refs_asrt
>             "Assert that `sym_refs (state_refs_of' s)` holds"
>         stateAssert sch_act_wf_asrt
>             "Assert that `sch_act_wf (ksSchedulerAction s) s` holds"
>         stateAssert ksReadyQueues_asrt ""
>         ep <- getEndpoint epptr
>         case ep of
>             IdleEP ->
>                 return ()
>             _ -> do
>                 assert (distinct (epQueue ep)) "the endpoint queue of ep must be a list of distinct pointers"
>                 setEndpoint epptr IdleEP
>                 forM_ (epQueue ep) (\t -> cancelAllIPC_loop_body t)
>                 rescheduleRequired

If a badged endpoint is recycled, then cancel every pending send operation using a badge equal to the recycled capability's badge. Receive operations are not affected.

> cancelBadgedSends :: PPtr Endpoint -> Word -> Kernel ()
> cancelBadgedSends epptr badge = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     stateAssert sch_act_wf_asrt
>         "Assert that `sch_act_wf (ksSchedulerAction s) s` holds"
>     stateAssert ksReadyQueues_asrt ""
>     ep <- getEndpoint epptr
>     case ep of
>         IdleEP -> return ()
>         RecvEP {} -> return ()
>         SendEP queue -> do
>             assert (distinct queue) "queue must be a list of distinct pointers"
>             setEndpoint epptr IdleEP
>             queue' <- (flip filterM queue) $ \t -> do
>                 st <- getThreadState t
>                 if blockingIPCBadge st == badge
>                     then do
>                         restartThreadIfNoFault t
>                         return False
>                     else return True
>             ep' <- case queue' of
>                 [] -> return IdleEP
>                 _ -> return $ SendEP { epQueue = queue' }
>             setEndpoint epptr ep'
>             rescheduleRequired

\subsection{Accessing Endpoints}

The following two functions are specialisations of "getObject" and
"setObject" for the endpoint object and pointer types.

> getEndpoint :: PPtr Endpoint -> Kernel Endpoint
> getEndpoint = getObject

> setEndpoint :: PPtr Endpoint -> Endpoint -> Kernel ()
> setEndpoint = setObject

> epBlocked :: ThreadState -> Maybe (PPtr Endpoint)
> epBlocked ts = case ts of
>     BlockedOnReceive r _ _ -> Just r
>     BlockedOnSend r _ _ _ _ -> Just r
>     _ -> Nothing

> getBlockingObject :: ThreadState -> Kernel (PPtr Endpoint)
> getBlockingObject ts = do
>     epOpt <- return $ epBlocked ts
>     assert (epOpt /= Nothing) "getBlockingObject: endpoint must not be Nothing"
>     return $ fromJust epOpt

> getEpQueue :: Endpoint -> Kernel [PPtr TCB]
> getEpQueue ep =
>     case ep of
>         SendEP q -> return q
>         RecvEP q -> return q
>         _ -> fail "getEpQueue: endpoint must not be idle"

> updateEpQueue :: Endpoint -> [PPtr TCB] -> Endpoint
> updateEpQueue (RecvEP _) q' = RecvEP q'
> updateEpQueue (SendEP _) q' = SendEP q'
> updateEpQueue _ _ = IdleEP

> reorderEp :: PPtr Endpoint -> PPtr TCB -> Kernel ()
> reorderEp epPtr tptr = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     ep <- getEndpoint epPtr
>     qs <- getEpQueue ep
>     qs' <- tcbEPDequeue tptr qs
>     qs'' <- tcbEPAppend tptr qs'
>     setEndpoint epPtr (updateEpQueue ep qs'')
