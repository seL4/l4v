%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module specifies the contents and behaviour of a synchronous IPC endpoint.

> module SEL4.Object.Endpoint (
>         sendIPC, receiveIPC,
>         cancelIPC, cancelAllIPC, cancelBadgedSends, epBlocked, tcbAppend, reorderEp
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: cancelIPC tcbAppend #-}

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
>         stateAssert invs'_asrt "`invs'`"
>         stateAssert sym_refs_asrt "`sym_refs (state_refs_of' s)`"
>         stateAssert valid_idle'_asrt "`valid_idle'`"
>         stateAssert (active_tcb_at'_asrt thread)
>             "`thread` has an `active'` thread state"
>         ep <- getEndpoint epptr
>         case epState ep of

If the endpoint is idle, and this is a blocking IPC operation, then the current thread is queued in the endpoint, which changes to the sending state. The thread will block until a receive operation is performed on the endpoint.

>             IdleEPState | blocking -> do
>                 setThreadState (BlockedOnSend {
>                     blockingObject = epptr,
>                     blockingIPCBadge = badge,
>                     blockingIPCCanGrant = canGrant,
>                     blockingIPCCanGrantReply = canGrantReply,
>                     blockingIPCIsCall = call }) thread
>                 tcbEPAppend thread epptr SendEPState

If the endpoint is already in the sending state, and this is a blocking IPC operation, then the current thread is blocked and added to the queue.

>             SendEPState | blocking -> do
>                 setThreadState (BlockedOnSend {
>                     blockingObject = epptr,
>                     blockingIPCBadge = badge,
>                     blockingIPCCanGrant = canGrant,
>                     blockingIPCCanGrantReply = canGrantReply,
>                     blockingIPCIsCall = call }) thread
>                 tcbEPAppend thread epptr SendEPState

A non-blocking IPC to an idle or sending endpoint will be silently dropped.

>             IdleEPState -> return ()
>             SendEPState -> return ()

If the endpoint is receiving, then a thread is removed from its queue, and an IPC transfer is performed. If the recipient is the last thread in the endpoint's queue, the endpoint becomes idle.

>             ReceiveEPState -> do
>                 let q = epQueue ep
>                 stateAssert (tcb_queue_head_end_valid_asrt q) ""
>                 assert (not (tcbQueueEmpty q)) "Receive endpoint queue must not be empty"
>                 let dest = fromJust $ tcbQueueHead q
>                 assert (dest /= thread) "thread must not be the head of the queue"
>                 stateAssert (not_tcbQueued_asrt dest) ""
>                 stateAssert (not_tcbInReleaseQueue_asrt dest) ""
>                 action <- getSchedulerAction
>                 assert (action /= SwitchToThread dest) ""
>                 tcbEPDequeue dest epptr
>                 recvState <- getThreadState dest
>                 assert (isReceive recvState)
>                        "TCB in receive endpoint queue must be blocked on receive"
>                 doIPCTransfer thread (Just epptr) badge canGrant dest
>                 let replyOpt = replyObject recvState
>                 stateAssert (valid_bound_reply'_asrt replyOpt) ""
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
>                     assert (scOptSrc /= Nothing) ""
>                     schedContextDonate (fromJust scOptSrc) dest


The receiving thread has now completed its blocking operation and can run. If the receiving thread has higher priority than the current thread, the scheduler is instructed to switch to it immediately.

>                 setThreadState Running dest
>                 scOpt <- threadGet tcbSchedContext dest
>                 ifCondRefillUnblockCheck scOpt (Just False) (Just False)
>                 possibleSwitchTo dest

\subsection{Receiving IPC}

The IPC receive operation is essentially the same as the send operation, but with the send and receive states swapped. There are a few other differences: the badge must be retrieved from the TCB when completing an operation, and is not set when adding a TCB to the queue; also, the operation always blocks if no partner is immediately available; lastly, the receivers thread state does not need updating to Running however the senders state may.

> isTimeoutFault :: Fault -> Bool
> isTimeoutFault (Timeout _) = True
> isTimeoutFault _ = False

> receiveIPCBlocked :: Bool -> PPtr TCB -> PPtr Endpoint -> Maybe (PPtr Reply) -> Kernel ()
> receiveIPCBlocked isBlocking thread epptr replyOpt = do
>     case isBlocking of
>         True -> do
>             setThreadState (BlockedOnReceive {
>                 blockingObject = epptr,
>                 blockingIPCCanGrant = False,
>                 replyObject = replyOpt}) thread
>             when (replyOpt /= Nothing) $
>                 updateReply (fromJust replyOpt) (\reply -> reply { replyTCB = Just thread })
>             tcbEPAppend thread epptr ReceiveEPState
>         False -> doNBRecvFailedTransfer thread

> receiveIPC :: PPtr TCB -> Capability -> Bool -> Capability -> Kernel ()
> receiveIPC thread cap@(EndpointCap {}) isBlocking replyCap = do
>         let epptr = capEPPtr cap
>         stateAssert sym_refs_asrt "`sym_refs (state_refs_of' s)`"
>         stateAssert sch_act_wf_asrt "`sch_act_wf (ksSchedulerAction s) s`"
>         stateAssert valid_idle'_asrt "`valid_idle'`"
>         assert (isReplyCap replyCap || isNullCap replyCap) "replyCap must be either a reply cap or a null cap"
>         replyOpt <- (case replyCap of
>             ReplyCap r _ -> return (Just r)
>             NullCap -> return Nothing
>             _ -> fail "receiveIPC: replyCap must be ReplyCap or NullCap")
>         when (replyOpt /= Nothing) $ do
>             tptrOpt <- liftM replyTCB (getReply (fromJust replyOpt))
>             when (tptrOpt /= Nothing && tptrOpt /= Just thread) $ do
>                 cancelIPC $ fromJust tptrOpt
>         stateAssert (valid_bound_reply'_asrt replyOpt) ""
>         ep <- getEndpoint epptr
>         -- check if anything is waiting on bound ntfn
>         ntfnPtr <- getBoundNotification thread
>         ntfn <- maybe (return $ Notification IdleNtfnState emptyQueue Nothing Nothing Nothing) getNotification ntfnPtr
>         if (isJust ntfnPtr && ntfnState ntfn == Active)
>           then completeSignal (fromJust ntfnPtr) thread
>           else do
>             when (ntfnPtr /= Nothing && isBlocking) $
>               maybeReturnSc (fromJust ntfnPtr) thread
>             case epState ep of
>               IdleEPState -> receiveIPCBlocked isBlocking thread epptr replyOpt
>               ReceiveEPState -> receiveIPCBlocked isBlocking thread epptr replyOpt
>               SendEPState -> do
>                 let q = epQueue ep
>                 stateAssert (tcb_queue_head_end_valid_asrt q) ""
>                 assert (not (tcbQueueEmpty q)) "Send endpoint queue must not be empty"
>                 let sender = fromJust $ tcbQueueHead q
>                 tcbEPDequeue sender epptr
>                 senderState <- getThreadState sender
>                 assert (isSend senderState)
>                        "TCB in send endpoint queue must be blocked on send"
>                 let badge = blockingIPCBadge senderState
>                 let canGrant = blockingIPCCanGrant senderState
>                 let canGrantReply = blockingIPCCanGrantReply senderState
>                 doIPCTransfer sender (Just epptr) badge canGrant thread
>                 scOpt <- threadGet tcbSchedContext sender
>                 ifCondRefillUnblockCheck scOpt (Just False) (Just True)
>                 let call = blockingIPCIsCall senderState
>                 fault <- threadGet tcbFault sender
>                 if (call || isJust fault)
>                     then if ((canGrant || canGrantReply) && replyOpt /= Nothing)
>                         then do
>                             senderSc <- threadGet tcbSchedContext sender
>                             donate <- return ((senderSc /= Nothing) && not (isJust fault && isTimeoutFault (fromJust fault)))
>                             replyPush sender thread (fromJust replyOpt) donate
>                         else setThreadState Inactive sender
>                     else do
>                         setThreadState Running sender
>                         possibleSwitchTo sender

> receiveIPC _ _ _ _ = fail "receiveIPC: invalid cap"

\subsection{Cancelling IPC}

If a thread is waiting for an IPC operation, it may be necessary to move the thread into a state where it is no longer waiting; for example if the thread is deleted. The following function, given a pointer to a thread, cancels any IPC that thread is involved in.

> cancelIPC :: PPtr TCB -> Kernel ()
> cancelIPC tptr = do
>         stateAssert sym_refs_asrt "`sym_refs (state_refs_of' s)`"
>         stateAssert ready_qs_runnable "threads in the ready queues are runnable'"
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
>     stateAssert (valid_bound_reply'_asrt replyOpt) ""
>     epptr <- getBlockingObject state
>     stateAssert (ep_at'_asrt epptr) ""
>     tcbEPDequeue tptr epptr
>     case replyOpt of
>         Nothing -> return ()
>         Just reply -> replyUnlink reply tptr

Finally, replace the IPC block with a fault block (which will retry the operation if the thread is resumed).

>     setThreadState Inactive tptr

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

> removeAndRestartEPQueuedThread :: PPtr TCB -> PPtr Endpoint -> Kernel ()
> removeAndRestartEPQueuedThread t epptr = do
>         st <- getThreadState t
>         assert (isSend st || isReceive st) "TCB in endpoint queue must be blocked on send or receive"
>         tcbEPDequeue t epptr
>         st <- getThreadState t
>         let replyOpt = if isReceive st then replyObject st else Nothing
>         stateAssert (valid_bound_reply'_asrt replyOpt) ""
>         case replyOpt of
>             Nothing -> return ()
>             Just reply -> replyUnlink reply t
>         restartThreadIfNoFault t

If an endpoint is deleted, then every pending IPC operation using it must be cancelled.

> cancelAllIPC :: PPtr Endpoint -> Kernel ()
> cancelAllIPC epptr = do
>         stateAssert sch_act_wf_asrt "`sch_act_wf (ksSchedulerAction s) s`"
>         stateAssert ksReadyQueues_asrt ""
>         ep <- getEndpoint epptr
>         case epState ep of
>             IdleEPState ->
>                 return ()
>             _ -> do
>                 let q = epQueue ep
>                 stateAssert (tcb_queue_head_end_valid_asrt q) ""
>                 whileLoop (\ptrOpt -> const (ptrOpt /= Nothing))
>                           (\ptrOpt -> do
>                                assert (ptrOpt /= Nothing) "the option type must not be Nothing"
>                                ptr <- return $ fromJust ptrOpt
>                                next <- threadGet tcbSchedNext ptr
>                                removeAndRestartEPQueuedThread ptr epptr
>                                return next)
>                           (tcbQueueHead q)
>                 ep <- getEndpoint epptr
>                 assert (epState ep == IdleEPState) "the endpoint must now be idle"
>                 rescheduleRequired

If a badged endpoint is recycled, then cancel every pending send operation using a badge equal to the recycled capability's badge. Receive operations are not affected.

> removeAndRestartBadgedThread :: PPtr TCB -> PPtr Endpoint -> Word -> Kernel ()
> removeAndRestartBadgedThread t epptr badge = do
>     st <- getThreadState t
>     assert (isSend st) "TCB in send endpoint queue must be blocked on send"
>     when (blockingIPCBadge st == badge) $ do
>         tcbEPDequeue t epptr
>         restartThreadIfNoFault t

> cancelBadgedSends :: PPtr Endpoint -> Word -> Kernel ()
> cancelBadgedSends epptr badge = do
>     stateAssert sch_act_wf_asrt "`sch_act_wf (ksSchedulerAction s) s`"
>     stateAssert ksReadyQueues_asrt ""
>     ep <- getEndpoint epptr
>     case epState ep of
>         IdleEPState -> return ()
>         ReceiveEPState -> return ()
>         SendEPState -> do
>             let q = epQueue ep
>             stateAssert (tcb_queue_head_end_valid_asrt q) ""
>             whileLoop (\ptrOpt -> const (ptrOpt /= Nothing))
>                       (\ptrOpt -> do
>                            assert (ptrOpt /= Nothing) "the option type must not be Nothing"
>                            ptr <- return $ fromJust ptrOpt
>                            next <- threadGet tcbSchedNext ptr
>                            removeAndRestartBadgedThread ptr epptr badge
>                            return next)
>                       (tcbQueueHead q)
>             rescheduleRequired

\subsection{Accessing Endpoints}

The following two functions are specialisations of "getObject" and
"setObject" for the endpoint object and pointer types.

> getEndpoint :: PPtr Endpoint -> Kernel Endpoint
> getEndpoint = getObject

> setEndpoint :: PPtr Endpoint -> Endpoint -> Kernel ()
> setEndpoint = setObject

> updateEndpoint :: PPtr Endpoint -> (Endpoint -> Endpoint) -> Kernel ()
> updateEndpoint epPtr upd = do
>     ep <- getEndpoint epPtr
>     setEndpoint epPtr (upd ep)

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

> tcbEPDequeue :: PPtr TCB -> PPtr Endpoint -> Kernel ()
> tcbEPDequeue tcbPtr epPtr = do
>     ep <- getEndpoint epPtr
>     q' <- tcbQueueRemove (epQueue ep) tcbPtr
>     updateEndpoint epPtr (\ep -> ep { epQueue = q' })
>     when (tcbQueueEmpty q') $
>         updateEndpoint epPtr (\ep -> ep { epState = IdleEPState })

> tcbAppend :: PPtr TCB -> TcbQueue -> Kernel TcbQueue
> tcbAppend tcbPtr q = do
>     stateAssert (orderedInsertBackwards_asrt tcbPtr q (threadRead tcbPriority) (>=)) ""
>     orderedInsert tcbPtr q (threadRead tcbPriority) (>=)

> tcbEPAppend :: PPtr TCB -> PPtr Endpoint -> EPState -> Kernel ()
> tcbEPAppend tcbPtr epPtr state = do
>     stateAssert (not_sched_linked_asrt tcbPtr) ""
>     ep <- getEndpoint epPtr
>     stateAssert (tcb_queue_head_end_valid_asrt (epQueue ep)) ""
>     q' <- tcbAppend tcbPtr (epQueue ep)
>     updateEndpoint epPtr (\ep -> ep { epQueue = q' })
>     updateEndpoint epPtr (\ep -> ep { epState = state })

> reorderEp :: PPtr Endpoint -> PPtr TCB -> Kernel ()
> reorderEp epPtr tptr = do
>     ep <- getEndpoint epPtr
>     q' <- tcbQueueRemove (epQueue ep) tptr
>     q'' <- tcbAppend tptr q'
>     updateEndpoint epPtr (\ep -> ep { epQueue = q'' })
