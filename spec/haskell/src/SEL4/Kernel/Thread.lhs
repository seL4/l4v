%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains the scheduler, and miscellaneous functions that manipulate thread state.

\begin{impdetails}

We use the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Kernel.Thread where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Model SEL4.Machine SEL4.Object.Structures SEL4.Object.Instances() SEL4.API.Types #-}
% {-# BOOT-EXPORTS: setDomain setMCPriority setPriority getThreadState setThreadState setBoundNotification getBoundNotification doIPCTransfer isRunnable restart suspend  doReplyTransfer tcbQueueEmpty tcbQueuePrepend tcbQueueAppend tcbQueueInsert tcbQueueRemove tcbSchedEnqueue tcbSchedDequeue rescheduleRequired scheduleTCB getSchedulable possibleSwitchTo endTimeslice inReleaseQueue tcbReleaseRemove tcbSchedAppend switchToThread #-}

> import Prelude hiding (Word)
> import SEL4.Config
> import SEL4.API.Types
> import SEL4.API.Failures(Fault(..))
> import SEL4.API.Faults
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object
> import SEL4.Object.Reply
> import SEL4.Object.SchedContext
> import SEL4.Object.Structures
> import SEL4.Kernel.VSpace
> import {-# SOURCE #-} SEL4.Kernel.FaultHandler(handleTimeout, isValidTimeoutHandler)
> import {-# SOURCE #-} SEL4.Kernel.Init

> import Data.Bits hiding (countLeadingZeros)
> import Data.Array
> import Data.WordLib
> import Data.Maybe(fromJust, isJust)
> import Data.Set(fromList, member)

\end{impdetails}

The architecture-specific definitions are imported qualified with the "Arch" prefix.

> import qualified SEL4.Kernel.Thread.TARGET as Arch

\subsection{Idle Thread Creation}

The idle thread must halt execution and wait for an interrupt to occur, at which point the kernel will be re-entered with an Interrupt event. The following function configures a given TCB to do this when activated.

> configureIdleThread :: PPtr TCB -> KernelInit ()
> configureIdleThread tcb = do
>     Arch.configureIdleThread tcb
>     doKernelOp $ setThreadState IdleThreadState tcb

\subsection{Initial Thread Creation}

This function activates the initial user-level thread. It sets the
first argument register and the program counter, sets the thread's
state so it can be scheduled, and then switches to the thread.
The initial user-level thread has the right to change the security domains of other threads.

> activateInitialThread :: PPtr TCB -> VPtr -> VPtr -> Kernel ()
> activateInitialThread threadPtr entry infoPtr = do
>         asUser threadPtr $ setRegister capRegister $ fromVPtr infoPtr
>         asUser threadPtr $ setNextPC $ fromVPtr entry
>         setThreadState Running threadPtr
>         setSchedulerAction ResumeCurrentThread
>         idle <- getIdleThread
>         setCurThread idle
>         switchToThread threadPtr

\subsection{Thread Activation}

The "activateThread" function is used to prepare a thread to run. If the thread is in the "Restart" state, then it is running for the first time, resuming after a fault, or restarting an aborted system call; in any of these cases, it will start running at the current instruction. Otherwise, it starts running at the next instruction.

> activateThread :: Kernel ()
> activateThread = do
>         thread <- getCurThread
>         scPtrOpt <- threadGet tcbYieldTo thread
>         when (scPtrOpt /= Nothing) $ do
>             schedContextCompleteYieldTo thread
>         state <- getThreadState thread
>         case state of
>             Running -> return ()
>             Restart -> do
>                 pc <- asUser thread $ getRestartPC
>                 asUser thread $ setNextPC pc
>                 setThreadState Running thread
>             IdleThreadState -> do
>                 Arch.activateIdleThread thread
>             _ -> fail $ "Current thread is blocked, state: " ++ show state

\subsection{Thread State}

The following function is used by the scheduler to determine whether a
particular thread is ready to run. Note that the idle thread is not considered
runnable; this is to prevent it being inserted in the scheduler queue.

> readRunnable :: PPtr TCB -> KernelR Bool
> readRunnable thread = do
>         state <- threadRead tcbState thread
>         return $ case state of
>             Running -> True
>             Restart -> True
>             _ -> False

> isRunnable :: PPtr TCB -> Kernel Bool
> isRunnable thread = getsJust (readRunnable thread)

> readSchedulable :: PPtr TCB -> KernelR Bool
> readSchedulable tcbPtr = do
>     runnable <- readRunnable tcbPtr
>     scPtrOpt <- threadRead tcbSchedContext tcbPtr
>     readStateAssert valid_tcbs'_asrt "valid_tcbs' holds"
>     if scPtrOpt == Nothing
>         then return False
>         else do
>             let scPtr = fromJust scPtrOpt
>             active <- readScActive scPtr
>             inReleaseQ <- readInReleaseQueue tcbPtr
>             return $ runnable && active && not inReleaseQ

> getSchedulable :: PPtr TCB -> Kernel Bool
> getSchedulable tcbPtr = getsJust (readSchedulable tcbPtr)

\subsubsection{Suspending a Thread}

When a thread is suspended, either explicitly by a TCB invocation or implicitly when it is being destroyed, any operation that it is currently performing must be cancelled.

> updateRestartPC :: PPtr TCB -> Kernel ()
> updateRestartPC tcb =
>     asUser tcb (getRegister nextInstructionRegister
>                 >>= setRegister faultRegister)

> suspend :: PPtr TCB -> Kernel ()
> suspend target = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     cancelIPC target
>     state <- getThreadState target
>     if state == Running then updateRestartPC target else return ()
>     setThreadState Inactive target
>     tcbSchedDequeue target
>     tcbReleaseRemove target
>     schedContextCancelYieldTo target

\subsubsection{Restarting a Blocked Thread}

The Restart operation forces a thread that has blocked to retry the operation that caused it to block.

The invoked thread will return to the instruction that caused it to enter the kernel prior to blocking. If an IPC is in progress (including a fault IPC), it will be silently aborted. Beware of doing this to restart an atomic send and receive operation --- the thread will retry the send phase, even if it had previously succeeded in sending the message and was waiting for the receive phase to complete.

> restart :: PPtr TCB -> Kernel ()
> restart target = do
>     stopped <- isStopped target
>     scOpt <- threadGet tcbSchedContext target
>     when stopped $ do
>         cancelIPC target
>         setThreadState Restart target
>         ifCondRefillUnblockCheck scOpt (Just True) (Just False)
>         when (isJust scOpt) $ schedContextResume (fromJust scOpt)
>         schedulable <- getSchedulable target
>         when schedulable $ possibleSwitchTo target

\subsection{IPC Transfers}

The following function is called before resuming or suspending execution of a thread that has a pending IPC transfer. It looks up the sender and receiver's message buffers (in that order, and skipping the send buffer for a fault IPC), and then transfers the message.

If either of the buffers is missing, then the message will be truncated to include only the part not stored in the buffer.

> doIPCTransfer ::
>         PPtr TCB -> Maybe (PPtr Endpoint) -> Word -> Bool ->
>         PPtr TCB -> Kernel ()
> doIPCTransfer sender endpoint badge grant receiver = do
>         receiveBuffer <- lookupIPCBuffer True receiver
>         fault <- threadGet tcbFault sender

>         case fault of

For normal IPC messages, the message registers are transferred.

>             Nothing -> do
>                 sendBuffer <- lookupIPCBuffer False sender
>                 doNormalTransfer
>                     sender sendBuffer endpoint badge grant
>                     receiver receiveBuffer

If the sent message is a fault IPC, the stored fault is transferred.

>             Just _ -> do
>                 doFaultTransfer badge sender receiver receiveBuffer

Replies sent by the "Reply" and "ReplyRecv" system calls can either be normal IPC replies, or fault replies. In the former case, the transfer is the same as for an IPC send, but there is never a fault, capability grants are always allowed, and the badge is always 0.

> doReplyTransfer :: PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> doReplyTransfer sender reply grant = do
>     receiverOpt <- liftM replyTCB (getReply reply)
>     case receiverOpt of
>         Nothing -> return ()
>         Just receiver -> do
>             state <- getThreadState receiver
>             if not $ isReply state
>                 then return ()
>                 else do
>                     replyRemove reply receiver
>                     scOpt <- threadGet tcbSchedContext receiver
>                     ifCondRefillUnblockCheck scOpt (Just True) (Just False)
>                     faultOpt <- threadGet tcbFault receiver
>                     case faultOpt of
>                         Nothing -> do
>                             doIPCTransfer sender Nothing 0 grant receiver
>                             setThreadState Running receiver
>                         Just fault -> do
>                             mi <- getMessageInfo sender
>                             buf <- lookupIPCBuffer False sender
>                             mrs <- getMRs sender buf mi
>                             restart <- handleFaultReply fault receiver (msgLabel mi) mrs
>                             threadSet (\tcb -> tcb { tcbFault = Nothing }) receiver
>                             setThreadState (if restart then Restart else Inactive) receiver
>                     runnable <- isRunnable receiver
>                     scPtrOpt <- threadGet tcbSchedContext receiver
>                     when (scPtrOpt /= Nothing && runnable) $ do
>                         let scPtr = fromJust scPtrOpt
>                         ready <- refillReady scPtr
>                         sufficient <- getRefillSufficient scPtr 0
>                         if ready && sufficient
>                             then possibleSwitchTo receiver
>                             else do
>                                 sc <- getSchedContext scPtr
>                                 isHandlerValid <- isValidTimeoutHandler receiver
>                                 isTimeout <- case faultOpt of
>                                     Just (Timeout _) -> return True
>                                     _ -> return False
>                                 if isHandlerValid && not isTimeout
>                                     then handleTimeout receiver $ Timeout $ scBadge sc
>                                     else postpone scPtr

\subsubsection{Ordinary IPC}

Ordinary IPC simply transfers all message registers. It requires pointers to the source and destination threads, and also to their respective IPC buffers.

> doNormalTransfer ::
>     PPtr TCB -> Maybe (PPtr Word) -> Maybe (PPtr Endpoint) -> Word -> Bool ->
>     PPtr TCB -> Maybe (PPtr Word) -> Kernel ()
> doNormalTransfer sender sendBuffer endpoint badge canGrant
>         receiver receiveBuffer = do
>         tag <- getMessageInfo sender
>         caps <- if canGrant
>             then lookupExtraCaps sender sendBuffer tag
>                 `catchFailure` const (return [])
>             else return []
>         msgTransferred <- copyMRs sender sendBuffer receiver receiveBuffer $
>                                   msgLength tag
>         tag' <- transferCaps tag caps endpoint receiver receiveBuffer
>         let tag'' = tag' { msgLength = msgTransferred }
>         setMessageInfo receiver tag''
>         asUser receiver $ setRegister badgeRegister badge

\subsubsection{Fault IPC}

If the message is a fault --- either just generated, or loaded from the sender's TCB --- then it will be transferred instead of the sender's message registers. In this case, no pointer to the sender's buffer is required.

The recipient's argument registers are filled in with various information about the nature of the fault and the present state of the faulting thread.

> doFaultTransfer :: Word -> PPtr TCB -> PPtr TCB -> Maybe (PPtr Word) ->
>         Kernel ()
> doFaultTransfer badge sender receiver receiverIPCBuffer = do
>         fault <- threadGet tcbFault sender
>         f <- case fault of
>             Just f -> return f
>             Nothing -> fail "doFaultTransfer: no fault found"
>         (faultLabel, faultMsg) <- makeFaultMessage f sender
>         sent <- setMRs receiver receiverIPCBuffer faultMsg
>         let msgInfo = MI {
>              msgLength = sent,
>              msgExtraCaps = 0,
>              msgCapsUnwrapped = 0,
>              msgLabel = faultLabel }
>         setMessageInfo receiver msgInfo
>         asUser receiver $ setRegister badgeRegister badge

\subsubsection{IPC Capability Transfers}

This function is called when an IPC message includes a capability to transfer. It attempts to perform the transfer, and returns an adjusted messageInfo containing the number of caps transferred and the bitmask of which caps were unwrapped.

> transferCaps :: MessageInfo -> [(Capability, PPtr CTE)] ->
>         Maybe (PPtr Endpoint) -> PPtr TCB -> Maybe (PPtr Word) ->
>         Kernel MessageInfo
> transferCaps info caps endpoint receiver receiveBuffer = do
>     destSlots <- getReceiveSlots receiver receiveBuffer
>     let info' = info { msgExtraCaps = 0, msgCapsUnwrapped = 0 }
>     case receiveBuffer of
>         Nothing -> return info'
>         Just rcvBuffer -> do
>             transferCapsToSlots endpoint rcvBuffer 0
>                 caps destSlots info'

> transferCapsToSlots :: Maybe (PPtr Endpoint) -> PPtr Word -> Int ->
>        [(Capability, PPtr CTE)] -> [PPtr CTE] -> MessageInfo ->
>        Kernel MessageInfo
> transferCapsToSlots _ _ n [] _ mi =
>     return $ mi { msgExtraCaps = fromIntegral n }
> transferCapsToSlots ep rcvBuffer n (capWithSrcSlot:caps) slots mi =
>     constOnFailure (mi { msgExtraCaps = fromIntegral n }) $ do
>         case (cap, ep, slots) of
>             (EndpointCap { capEPPtr = p1 }, Just p2, _) | p1 == p2 -> do
>                 withoutFailure $
>                     setExtraBadge rcvBuffer (capEPBadge cap) n
>                 withoutFailure $ transferAgain slots miCapUnfolded
>             (_, _, destSlot:slots') -> do
>                 cap' <- unifyFailure $ deriveCap srcSlot $ cap
>                 when (isNullCap cap') $ throw undefined
>                 withoutFailure $ cteInsert cap' srcSlot destSlot
>                 withoutFailure $ transferAgain slots' mi
>             _ -> return $ mi { msgExtraCaps = fromIntegral n }
>     where
>        transferAgain = transferCapsToSlots ep rcvBuffer (n + 1) caps
>        miCapUnfolded = mi { msgCapsUnwrapped = msgCapsUnwrapped mi .|. bit n}
>        (cap, srcSlot) = capWithSrcSlot

\subsubsection{Notification Objects}

In the case of notification, the badge from the notification object's data word is loaded into the receiver's badge.

\subsection{Scheduling}

\subsubsection{The Scheduler}

The scheduler will perform one of three actions, depending on the scheduler action field of the global kernel state.

This extra check matches an optimisation in the C fast path, which shortcuts
checking the scheduler bitmaps using implicit knowledge that the current thread
has the highest runnable priority in the system on kernel entry (unless idle).

> scheduleChooseNewThread :: Kernel ()
> scheduleChooseNewThread = do
>     stateAssert ksReadyQueues_asrt ""
>     domainTime <- getDomainTime
>     when (domainTime == 0) $ nextDomain
>     chooseThread
>     setSchedulerAction ResumeCurrentThread

> scheduleSwitchThreadFastfail :: PPtr TCB -> PPtr TCB -> Priority -> Priority -> Kernel (Bool)
> scheduleSwitchThreadFastfail curThread idleThread curPrio targetPrio =
>     if curThread /= idleThread
>     then return (targetPrio < curPrio)
>     else return True

> checkDomainTime :: Kernel ()
> checkDomainTime = do
>     exp <- isCurDomainExpired
>     when exp $ do
>           setReprogramTimer True
>           rescheduleRequired

> scAndTimer :: Kernel ()
> scAndTimer = do
>     switchSchedContext
>     reprogram <- getReprogramTimer
>     when reprogram $ do
>         setNextInterrupt
>         setReprogramTimer False

> schedule :: Kernel ()
> schedule = do
>     stateAssert valid_idle'_asrt
>         "Assert that `valid_idle' s` holds"
>     stateAssert valid_domain_list'_asrt
>         "Assert that `valid_domain_list'` holds"
>     stateAssert sch_act_wf_asrt
>         "Assert that `sch_act_wf (ksSchedulerAction s) s` holds"
>     stateAssert cur_tcb'_asrt
>         "Assert that `cur_tcb' s` holds"
>     awaken
>     checkDomainTime
>     curThread <- getCurThread
>     action <- getSchedulerAction
>     case action of

The default action is to do nothing; the current thread will resume execution.

>         ResumeCurrentThread -> return ()

An IPC operation may request that the scheduler switch to a specific thread.
We check here that the candidate has the highest priority in the system.

>         SwitchToThread candidate -> do
>             isSchedulable <- getSchedulable curThread
>             when isSchedulable (tcbSchedEnqueue curThread)
>
>             idleThread <- getIdleThread
>             targetPrio <- threadGet tcbPriority candidate
>             curPrio <- threadGet tcbPriority curThread
>             fastfail <- scheduleSwitchThreadFastfail curThread idleThread curPrio targetPrio
>
>             curDom <- curDomain
>             highest <- isHighestPrio curDom targetPrio
>
>             if fastfail && not highest
>                 then do
>                     tcbSchedEnqueue candidate
>                     setSchedulerAction ChooseNewThread
>                     scheduleChooseNewThread
>                 else if isSchedulable && curPrio == targetPrio
>                     then do
>                         tcbSchedAppend candidate
>                         setSchedulerAction ChooseNewThread
>                         scheduleChooseNewThread
>                     else do
>                         switchToThread candidate
>                         setSchedulerAction ResumeCurrentThread

If the current thread is no longer runnable, has used its entire timeslice, an IPC cancellation has potentially woken multiple higher priority threads, or the domain timeslice is exhausted, then we scan the scheduler queues to choose a new thread. In the last case, we switch to the next domain beforehand.

>         ChooseNewThread -> do
>             isSchedulable <- getSchedulable curThread
>             when isSchedulable $ tcbSchedEnqueue curThread
>             scheduleChooseNewThread

>     scAndTimer
>     stateAssert ct_activatable'_asrt
>         "Assert that `ct_in_state' activatable' s` holds"


Threads are scheduled using a simple multiple-priority round robin algorithm.
It checks the priority bitmaps to find the highest priority with a non-empty
queue. It selects the first thread in that queue and makes it the current
thread.

Note that the ready queues are a separate structure in the kernel
model. In a real implementation, to avoid requiring
dynamically-allocated kernel memory, these queues would be linked
lists using the TCBs themselves as nodes.

Note also that the level 2 bitmap array is stored in reverse in order to get better cache locality for the more common case of higher priority threads.

> countLeadingZeros :: (Bits b, FiniteBits b) => b -> Int
> countLeadingZeros w =
>     length . takeWhile not . reverse . map (testBit w) $ [0 .. finiteBitSize w - 1]

> wordLog2 :: (Bits b, FiniteBits b) => b -> Int
> wordLog2 w = finiteBitSize w - 1 - countLeadingZeros w

> invertL1Index :: Int -> Int
> invertL1Index i = l2BitmapSize - 1 - i

> getHighestPrio :: Domain -> Kernel (Priority)
> getHighestPrio d = do
>     l1 <- getReadyQueuesL1Bitmap d
>     let l1index = wordLog2 l1
>     let l1indexInverted = invertL1Index l1index
>     l2 <- getReadyQueuesL2Bitmap d l1indexInverted
>     let l2index = wordLog2 l2
>     return $ l1IndexToPrio l1index .|. fromIntegral l2index

> isHighestPrio :: Domain -> Priority -> Kernel (Bool)
> isHighestPrio d p = do
>     l1 <- getReadyQueuesL1Bitmap d
>     if l1 == 0
>         then return True
>         else do
>             hprio <- getHighestPrio d
>             return (p >= hprio)

> chooseThread :: Kernel ()
> chooseThread = do
>     stateAssert ksReadyQueues_asrt ""
>     stateAssert ready_qs_runnable "threads in the ready queues are runnable'"
>     curdom <- if numDomains > 1 then curDomain else return 0
>     l1 <- getReadyQueuesL1Bitmap curdom
>     if l1 /= 0
>         then do
>             prio <- getHighestPrio curdom
>             queue <- getQueue curdom prio
>             let thread = fromJust $ tcbQueueHead queue
>             switchToThread thread
>         else
>             switchToIdleThread

> scheduleTCB :: PPtr TCB -> Kernel ()
> scheduleTCB tcbPtr = do
>     curThread <- getCurThread
>     action <- getSchedulerAction
>     schedulable <- getSchedulable tcbPtr
>     when (tcbPtr == curThread && action == ResumeCurrentThread && not schedulable) $ rescheduleRequired

\subsubsection{Switching Threads}

To switch to a new thread, we call the architecture-specific thread switch function, remove the new current thread from the ready queues, and then set the current thread pointer.

> switchToThread :: PPtr TCB -> Kernel ()
> switchToThread thread = do
>         runnable <- isRunnable thread
>         assert runnable "thread must be runnable"
>         stateAssert ksReadyQueues_asrt ""
>         stateAssert ready_qs_runnable "threads in the ready queues are runnable'"
>         Arch.switchToThread thread
>         tcbSchedDequeue thread
>         setCurThread thread

Switching to the idle thread is similar, except that we call a different architecture-specific idle thread switch function. Also, the conditional enqueue of the current thread is unnecessary, because we never switch to the idle thread when the current thread is runnable.

> switchToIdleThread :: Kernel ()
> switchToIdleThread = do
>         stateAssert ready_qs_runnable "threads in the ready queues are runnable'"
>         stateAssert valid_idle'_asrt
>             "Assert that `valid_idle' s` holds"
>         thread <- getIdleThread
>         Arch.switchToIdleThread
>         setCurThread thread

\subsubsection{Changing a Thread's Domain}

The following function is used to alter a thread's domain.

> setDomain :: PPtr TCB -> Domain -> Kernel ()
> setDomain tptr newdom = do
>         curThread <- getCurThread
>         tcbSchedDequeue tptr
>         threadSet (\t -> t { tcbDomain = newdom }) tptr
>         schedulable <- getSchedulable tptr
>         when schedulable $ tcbSchedEnqueue tptr
>         when (tptr == curThread) $ rescheduleRequired

\subsubsection{Changing a thread's MCP}

> setMCPriority :: PPtr TCB -> Priority -> Kernel ()
> setMCPriority tptr prio = do
>         threadSet (\t -> t { tcbMCP = prio }) tptr

\subsubsection{Changing a Thread's Priority}

> threadSetPriority :: PPtr TCB -> Priority -> Kernel ()
> threadSetPriority tptr prio = threadSet (\tcb -> tcb { tcbPriority = prio }) tptr

The following function is used to alter the priority of a thread.

> threadSetPriority_onRunning :: PPtr TCB -> Priority -> Kernel ()
> threadSetPriority_onRunning tptr prio = do
>     queued <- threadGet tcbQueued tptr
>     curThread <- getCurThread
>     if queued || tptr == curThread
>         then do
>              tcbSchedDequeue tptr
>              threadSetPriority tptr prio
>              tcbSchedEnqueue tptr
>              rescheduleRequired
>         else threadSetPriority tptr prio

> setPriority :: PPtr TCB -> Priority -> Kernel ()
> setPriority tptr prio = do
>     ts <- getThreadState tptr
>     case ts of
>          Running -> threadSetPriority_onRunning tptr prio
>          Restart -> threadSetPriority_onRunning tptr prio
>          _ -> do
>              threadSetPriority tptr prio
>              case (epBlocked ts) of
>                  Just ep -> reorderEp ep tptr
>                  _ -> return ()
>              case (ntfnBlocked ts) of
>                  Just ntfn -> reorderNtfn ntfn tptr
>                  _ -> return ()

\subsubsection{Switching to Woken Threads}

A successful IPC transfer will normally wake a thread other than the current
thread. At the point of waking we neither know whether the current thread will
block, or whether the woken thread has the highest priority.  We note the woken
thread as a candidate if it is a valid switch target, and examine its
importance in the scheduler. If the woken thread is not a viable switch
candidate, we enqueue it instead. In the case of multiple candidates, all
candidates are enqueued.

> possibleSwitchTo :: PPtr TCB -> Kernel ()
> possibleSwitchTo target = do
>     stateAssert valid_tcbs'_asrt "assert that `valid_tcbs'` holds"
>     scOpt <- threadGet tcbSchedContext target
>     inq <- inReleaseQueue target
>     when (scOpt /= Nothing && not inq) $ do
>         curDom <- curDomain
>         targetDom <- threadGet tcbDomain target
>         action <- getSchedulerAction
>         if (targetDom /= curDom)
>             then tcbSchedEnqueue target
>             else if (action /= ResumeCurrentThread)
>                 then do
>                     rescheduleRequired
>                     tcbSchedEnqueue target
>                 else setSchedulerAction $ SwitchToThread target

In most cases, the current thread has just sent a message to the woken thread, so we switch if the woken thread has the same or higher priority than the current thread; that is, whenever the priorities permit the switch.


\subsubsection{Cancelling Stored Scheduler Action}

This function is called when the system state has changed sufficiently that the stored scheduler action may be invalid. It safely discards any stored state and organises for a full reschedule to be performed.

> rescheduleRequired :: Kernel ()
> rescheduleRequired = do
>     action <- getSchedulerAction
>     case action of
>         SwitchToThread target -> do
>              sched <- getSchedulable target
>              when sched $ tcbSchedEnqueue target
>         _ -> return ()
>     setSchedulerAction ChooseNewThread

\subsubsection{Scheduling Parameters}

A trivial function is provided to fetch the current scheduler state of
a thread.

> getThreadState :: PPtr TCB -> Kernel ThreadState
> getThreadState = threadGet tcbState

When setting the scheduler state, we check for blocking of the current thread; in that case, we tell the scheduler to choose a new thread.

> setThreadState :: ThreadState -> PPtr TCB -> Kernel ()
> setThreadState ts tptr = do
>         threadSet (\t -> t { tcbState = ts }) tptr
>         scheduleTCB tptr

\subsubsection{Bound Notificaion objects}

> getBoundNotification :: PPtr TCB -> Kernel (Maybe (PPtr Notification))
> getBoundNotification = threadGet tcbBoundNotification

> setBoundNotification :: Maybe (PPtr Notification) -> PPtr TCB -> Kernel ()
> setBoundNotification ntfnPtr tptr = threadSet (\t -> t { tcbBoundNotification = ntfnPtr }) tptr

\subsubsection{Scheduler Queue Manipulation}

The following two functions place a thread at the beginning or end of its priority's ready queue, unless it is already queued.

%TODO: document

> prioToL1Index :: Priority -> Int
> prioToL1Index prio = fromIntegral $ prio `shiftR` wordRadix

> l1IndexToPrio :: Int -> Priority
> l1IndexToPrio i = (fromIntegral i) `shiftL` wordRadix

> getReadyQueuesL1Bitmap :: Domain -> Kernel (Word)
> getReadyQueuesL1Bitmap tdom = gets (\ks -> ksReadyQueuesL1Bitmap ks ! tdom)

> modifyReadyQueuesL1Bitmap :: Domain -> (Word -> Word) -> Kernel ()
> modifyReadyQueuesL1Bitmap tdom f = do
>     l1 <- getReadyQueuesL1Bitmap tdom
>     modify (\ks -> ks { ksReadyQueuesL1Bitmap =
>                             ksReadyQueuesL1Bitmap ks // [(tdom, f l1)]})

> getReadyQueuesL2Bitmap :: Domain -> Int -> Kernel (Word)
> getReadyQueuesL2Bitmap tdom i = gets (\ks -> ksReadyQueuesL2Bitmap ks ! (tdom, i))

> modifyReadyQueuesL2Bitmap :: Domain -> Int -> (Word -> Word) -> Kernel ()
> modifyReadyQueuesL2Bitmap tdom i f = do
>     l2 <- getReadyQueuesL2Bitmap tdom i
>     modify (\ks -> ks { ksReadyQueuesL2Bitmap =
>                             ksReadyQueuesL2Bitmap ks // [((tdom, i), f l2)]})

> addToBitmap :: Domain -> Priority -> Kernel ()
> addToBitmap tdom prio = do
>     let l1index = prioToL1Index prio
>     let l1indexInverted = invertL1Index l1index
>     let l2bit = fromIntegral ((fromIntegral prio .&. mask wordRadix)::Word)
>     modifyReadyQueuesL1Bitmap tdom $ \w -> w .|. bit l1index
>     modifyReadyQueuesL2Bitmap tdom l1indexInverted
>         (\w -> w .|. bit l2bit)

> removeFromBitmap :: Domain -> Priority -> Kernel ()
> removeFromBitmap tdom prio = do
>     let l1index = prioToL1Index prio
>     let l1indexInverted = invertL1Index l1index
>     let l2bit = fromIntegral((fromIntegral prio .&. mask wordRadix)::Word)
>     modifyReadyQueuesL2Bitmap tdom l1indexInverted $
>         (\w -> w .&. (complement $ bit l2bit))
>     l2 <- getReadyQueuesL2Bitmap tdom l1indexInverted
>     when (l2 == 0) $
>         modifyReadyQueuesL1Bitmap tdom $
>             (\w -> w .&. (complement $ bit l1index))

> tcbQueueEmpty :: TcbQueue -> Bool
> tcbQueueEmpty queue = tcbQueueHead queue == Nothing

> tcbQueuePrepend :: TcbQueue -> PPtr TCB -> Kernel TcbQueue
> tcbQueuePrepend queue tcbPtr = do
>     q <- if tcbQueueEmpty queue
>              then return $ queue { tcbQueueEnd = Just tcbPtr }
>              else do
>                  threadSet (\t -> t { tcbSchedNext = tcbQueueHead queue }) tcbPtr
>                  threadSet (\t -> t { tcbSchedPrev = Just tcbPtr }) (fromJust $ tcbQueueHead queue)
>                  return $ queue

>     return $ q { tcbQueueHead = Just tcbPtr}

> tcbQueueAppend :: TcbQueue -> PPtr TCB -> Kernel TcbQueue
> tcbQueueAppend queue tcbPtr = do
>     q <- if tcbQueueEmpty queue
>              then return $ queue { tcbQueueHead = Just tcbPtr }
>              else do
>                  threadSet (\t -> t { tcbSchedPrev = tcbQueueEnd queue }) tcbPtr
>                  threadSet (\t -> t { tcbSchedNext = Just tcbPtr }) (fromJust $ tcbQueueEnd queue)
>                  return $ queue

>     return $ q { tcbQueueEnd = Just tcbPtr}

Insert a thread into the middle of a queue, immediately before afterPtr, where afterPtr is not the head of the queue

> tcbQueueInsert :: PPtr TCB -> PPtr TCB -> Kernel ()
> tcbQueueInsert tcbPtr afterPtr = do
>    tcb <- getObject afterPtr
>    beforePtrOpt <- return $ tcbSchedPrev tcb
>    assert (beforePtrOpt /= Nothing) "afterPtr must not be the head of the list"
>    beforePtr <- return $ fromJust beforePtrOpt
>    assert (beforePtr /= afterPtr) "the tcbSchedPrev pointer of a TCB must never point to itself"

>    threadSet (\t -> t { tcbSchedPrev = Just beforePtr }) tcbPtr
>    threadSet (\t -> t { tcbSchedNext = Just afterPtr}) tcbPtr
>    threadSet (\t -> t { tcbSchedPrev = Just tcbPtr }) afterPtr
>    threadSet (\t -> t { tcbSchedNext = Just tcbPtr }) beforePtr

Remove a thread from a queue, which must originally contain the thread

> tcbQueueRemove :: TcbQueue -> PPtr TCB -> Kernel TcbQueue
> tcbQueueRemove queue tcbPtr = do
>     tcb <- getObject tcbPtr
>     beforePtrOpt <- return $ tcbSchedPrev tcb
>     afterPtrOpt <- return $ tcbSchedNext tcb

>     if tcbQueueHead queue == Just tcbPtr && tcbQueueEnd queue == Just tcbPtr

The queue is the singleton containing tcbPtr

>         then return $ TcbQueue { tcbQueueHead = Nothing, tcbQueueEnd = Nothing }
>         else
>             if tcbQueueHead queue == Just tcbPtr

tcbPtr is the head of the queue

>                 then do
>                     assert (afterPtrOpt /= Nothing) "the queue is not a singleton"
>                     threadSet (\t -> t { tcbSchedPrev = Nothing }) (fromJust $ afterPtrOpt)
>                     threadSet (\t -> t { tcbSchedNext = Nothing }) tcbPtr
>                     return $ queue { tcbQueueHead = afterPtrOpt }
>                 else
>                     if tcbQueueEnd queue == Just tcbPtr

tcbPtr is the end of the queue

>                         then do
>                             assert (beforePtrOpt /= Nothing) "the queue is not a singleton"
>                             threadSet (\t -> t { tcbSchedNext = Nothing }) (fromJust $ beforePtrOpt)
>                             threadSet (\t -> t { tcbSchedPrev = Nothing }) tcbPtr
>                             return $ queue { tcbQueueEnd = beforePtrOpt }
>                         else do

tcbPtr is in the middle of the queue

>                             assert (afterPtrOpt /= Nothing) "the queue is not a singleton"
>                             assert (beforePtrOpt /= Nothing) "the queue is not a singleton"
>                             threadSet (\t -> t { tcbSchedNext = afterPtrOpt }) (fromJust $ beforePtrOpt)
>                             threadSet (\t -> t { tcbSchedPrev = beforePtrOpt }) (fromJust $ afterPtrOpt)
>                             threadSet (\t -> t { tcbSchedPrev = Nothing }) tcbPtr
>                             threadSet (\t -> t { tcbSchedNext = Nothing }) tcbPtr
>                             return queue

> tcbSchedEnqueue :: PPtr TCB -> Kernel ()
> tcbSchedEnqueue thread = do
>     stateAssert ready_or_release'_asrt
>         "Assert that `ready_or_release'` holds"
>     stateAssert (not_tcbInReleaseQueue_asrt thread)
>         "thread must not have the tcbInReleaseQueue flag set"
>     stateAssert ksReadyQueues_asrt ""
>     stateAssert ksReleaseQueue_asrt ""
>     stateAssert valid_tcbs'_asrt "assert that `valid_tcbs'` holds"
>     runnable <- isRunnable thread
>     assert runnable "thread must be runnable"
>     queued <- threadGet tcbQueued thread
>     unless queued $ do
>         tdom <- threadGet tcbDomain thread
>         prio <- threadGet tcbPriority thread
>         queue <- getQueue tdom prio
>         when (tcbQueueEmpty queue) $ addToBitmap tdom prio
>         queue' <- tcbQueuePrepend queue thread
>         setQueue tdom prio queue'
>         threadSet (\t -> t { tcbQueued = True }) thread

> tcbSchedAppend :: PPtr TCB -> Kernel ()
> tcbSchedAppend thread = do
>     stateAssert ready_or_release'_asrt
>         "Assert that `ready_or_release'` holds"
>     stateAssert (not_tcbInReleaseQueue_asrt thread)
>         "thread must not have the tcbInReleaseQueue flag set"
>     stateAssert ksReadyQueues_asrt ""
>     stateAssert ksReleaseQueue_asrt ""
>     stateAssert valid_tcbs'_asrt "assert that `valid_tcbs'` holds"
>     runnable <- isRunnable thread
>     assert runnable "thread must be runnable"
>     queued <- threadGet tcbQueued thread
>     unless queued $ do
>         tdom <- threadGet tcbDomain thread
>         prio <- threadGet tcbPriority thread
>         queue <- getQueue tdom prio
>         when (tcbQueueEmpty queue) $ addToBitmap tdom prio
>         queue' <- tcbQueueAppend queue thread
>         setQueue tdom prio queue'
>         threadSet (\t -> t { tcbQueued = True }) thread

The following function dequeues a thread, if it is queued.

> tcbSchedDequeue :: PPtr TCB -> Kernel ()
> tcbSchedDequeue thread = do
>     stateAssert ready_or_release'_asrt
>         "Assert that `ready_or_release'` holds"
>     stateAssert ksReadyQueues_asrt ""
>     stateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     queued <- threadGet tcbQueued thread
>     when queued $ do
>         tdom <- threadGet tcbDomain thread
>         prio <- threadGet tcbPriority thread
>         queue <- getQueue tdom prio
>         queue' <- tcbQueueRemove queue thread
>         setQueue tdom prio queue'
>         threadSet (\t -> t { tcbQueued = False }) thread
>         when (tcbQueueEmpty queue') $ removeFromBitmap tdom prio

\section{Kernel Init}

Kernel init will created a initial thread whose tcbPriority is max priority.

> initTCB = (makeObject::TCB){ tcbPriority=maxBound }

> endTimeslice :: Bool -> Kernel ()
> endTimeslice canTimeoutFault = do
>     stateAssert cur_tcb'_asrt
>         "Assert that `cur_tcb' s` holds"
>     scPtr <- getCurSc
>     stateAssert (sc_at'_asrt scPtr) "there is a scheduling context at ksCurSc"
>     roundRobin <- isRoundRobin scPtr
>     ct <- getCurThread
>     valid <- isValidTimeoutHandler ct
>     if canTimeoutFault && not roundRobin && valid
>         then do
>             sc <- getSchedContext scPtr
>             handleTimeout ct $ Timeout $ scBadge sc
>         else do
>             ready <- refillReady scPtr
>             sufficient <- getRefillSufficient scPtr 0
>             if ready && sufficient
>                 then tcbSchedAppend ct
>                 else postpone scPtr

> readInReleaseQueue :: PPtr TCB -> KernelR Bool
> readInReleaseQueue tcbPtr = do
>     threadRead tcbInReleaseQueue tcbPtr

> inReleaseQueue :: PPtr TCB -> Kernel Bool
> inReleaseQueue tcbPtr = getsJust (readInReleaseQueue tcbPtr)

> tcbReleaseRemove :: PPtr TCB -> Kernel ()
> tcbReleaseRemove tcbPtr = do
>     stateAssert valid_tcbs'_asrt "assert that `valid_tcbs'` holds"
>     stateAssert ready_or_release'_asrt
>         "Assert that `ready_or_release'` holds"
>     stateAssert ksReleaseQueue_asrt ""
>     queued <- inReleaseQueue tcbPtr
>     when queued $ do
>         releaseQueue <- getReleaseQueue
>         when (tcbQueueHead releaseQueue == Just tcbPtr) $
>             setReprogramTimer True
>         new_queue <- tcbQueueRemove releaseQueue tcbPtr
>         setReleaseQueue new_queue
>         threadSet (\t -> t { tcbInReleaseQueue = False }) tcbPtr

%
