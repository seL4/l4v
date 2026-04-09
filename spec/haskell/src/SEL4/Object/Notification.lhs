%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module specifies the behavior of notification objects.

> module SEL4.Object.Notification (
>         sendSignal, receiveSignal,
>         cancelAllSignals, cancelSignal, completeSignal,
>         getNotification, setNotification, updateNotification, doUnbindNotification, unbindNotification,
>         unbindMaybeNotification, bindNotification, doNBRecvFailedTransfer,
>         ntfnBlocked, reorderNtfn
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: getNotification setNotification updateNotification #-}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.Endpoint(cancelIPC, tcbAppend)
> import SEL4.Object.SchedContext
> import {-# SOURCE #-} SEL4.Object.TCB
> import SEL4.Object.Instances()

> import {-# SOURCE #-} SEL4.Kernel.Thread

> import Data.Bits
> import Data.List
> import Data.Maybe(fromJust)
> import Data.Helpers (mapMaybe, distinct)

\end{impdetails}

\subsection{Sending Signals}

> -- helper function, FIXME redundant with Structure.isReceive
> receiveBlocked :: ThreadState -> Bool
> receiveBlocked st = case st of
>     BlockedOnReceive {} -> True
>     _ -> False

This function performs an signal operation, given a capability to a notification object, and a single machine word of message data (the badge). This operation will never block the signalling thread.

> sendSignal :: PPtr Notification -> Word -> Kernel ()

> sendSignal ntfnPtr badge = do

Fetch the notification object object, and select the operation based on its state.

>         stateAssert sym_refs_asrt "`sym_refs (state_refs_of' s)`"
>         nTFN <- getNotification ntfnPtr
>         case (ntfnState nTFN, ntfnBoundTCB nTFN) of

If the notification object is idle, store the badge and the value, and then
mark the notification object as active.

>             (IdleNtfnState, Just tcb) -> do
>                     state <- getThreadState tcb
>                     if (receiveBlocked state)
>                       then do
>                         cancelIPC tcb
>                         setThreadState Running tcb
>                         asUser tcb $ setRegister badgeRegister badge
>                         maybeDonateSc tcb ntfnPtr
>                         schedulable <- getSchedulable tcb
>                         when schedulable $ possibleSwitchTo tcb
>                         scOpt <- threadGet tcbSchedContext tcb
>                         ifCondRefillUnblockCheck scOpt (Just False) (Just False)
>                       else
>                         ntfnSetActive ntfnPtr badge
>             (IdleNtfnState, Nothing) -> ntfnSetActive ntfnPtr badge

If the notification object is waiting, a thread is removed from its queue and the signal is transferred to it.

>             (Waiting, _) -> do
>                 let q = ntfnQueue nTFN
>                 assert (not (tcbQueueEmpty q)) "the notification's queue cannot be empty"
>                 let dest = fromJust $ tcbQueueHead q
>                 st <- getThreadState dest
>                 assert (isNtfn st) "TCB in notification queue must be blocked on notification"
>                 tcbNTFNDequeue dest ntfnPtr
>                 setThreadState Running dest
>                 asUser dest $ setRegister badgeRegister badge
>                 maybeDonateSc dest ntfnPtr
>                 schedulable <- getSchedulable dest
>                 when schedulable $ possibleSwitchTo dest
>                 scOpt <- threadGet tcbSchedContext dest
>                 ifCondRefillUnblockCheck scOpt (Just False) (Just False)

If the notification object is active, new values are calculated and stored in the notification object. The calculation is done by a bitwise OR operation of the currently stored, and the newly sent values.

>             (Active, _) -> do
>                 let newBadge = badge .|. (fromJust $ ntfnMsgIdentifier nTFN)
>                 updateNotification ntfnPtr (\ntfn -> ntfn { ntfnMsgIdentifier = Just newBadge })

\subsection{Receiving Signals}

This function performs an receive signal operation, given a thread pointer and a capability to a notification object. The receive can be either blocking (the thread will be blocked on the notification until a signal arrives) or non-blocking depending on the isBlocking flag.

> doNBRecvFailedTransfer :: PPtr TCB -> Kernel ()
> doNBRecvFailedTransfer thread = asUser thread $ setRegister badgeRegister 0

> receiveSignalBlocked :: PPtr TCB -> PPtr Notification -> Bool -> Kernel ()
> receiveSignalBlocked thread ntfnPtr isBlocking = do
>     case isBlocking of
>         True -> do
>             setThreadState (BlockedOnNotification { waitingOnNotification = ntfnPtr } ) thread
>             tcbNTFNAppend thread ntfnPtr
>             maybeReturnSc ntfnPtr thread
>         False -> doNBRecvFailedTransfer thread

> receiveSignal :: PPtr TCB -> Capability -> Bool -> Kernel ()
> receiveSignal thread cap isBlocking = do

Fetch the notification object, and select the operation based on its state.

>         let ntfnPtr = capNtfnPtr cap
>         stateAssert sym_refs_asrt "`sym_refs (state_refs_of' s)`"
>         stateAssert valid_idle'_asrt "`valid_idle' s`"
>         runnable <- isRunnable thread
>         assert runnable "the thread must have a runnable' thread state"
>         stateAssert (not_sched_linked_asrt thread) ""
>         ntfn <- getNotification ntfnPtr
>         case ntfnState ntfn of

If the notification object is idle, then it becomes a waiting notification object, with the current thread in its queue. The thread is blocked.

>             IdleNtfnState -> receiveSignalBlocked thread ntfnPtr isBlocking

If the notification object is already waiting, the current thread is blocked and added to the queue. Note that this case cannot occur when the notification object is bound, as only the associated thread can wait on it.

>             Waiting -> receiveSignalBlocked thread ntfnPtr isBlocking

If the notification object is active, the badge of the invoked notification object capability will be loaded to the badge of the receiving thread and the notification object will be marked as idle.

>             Active -> do
>                 let badge = fromJust $ ntfnMsgIdentifier ntfn
>                 asUser thread $ setRegister badgeRegister badge
>                 updateNotification ntfnPtr (\notification -> notification { ntfnState = IdleNtfnState, ntfnMsgIdentifier = Nothing })
>                 maybeDonateSc thread ntfnPtr
>                 scOpt <- threadGet tcbSchedContext thread
>                 ifCondRefillUnblockCheck scOpt (Just False) (Just False)

\subsection{Delete Operation}

> removeAndRestartNTFNQueuedThread :: PPtr TCB -> PPtr Notification -> Kernel ()
> removeAndRestartNTFNQueuedThread t ntfnPtr = do
>     st <- getThreadState t
>     assert (isNtfn st) "TCB in notification queue must be blocked on notification"
>     tcbNTFNDequeue t ntfnPtr
>     setThreadState Restart t
>     scOpt <- threadGet tcbSchedContext t
>     ifCondRefillUnblockCheck scOpt (Just False) (Just True)
>     possibleSwitchTo t

If a notification object is deleted, then pending receive operations must be cancelled.

> cancelAllSignals :: PPtr Notification -> Kernel ()
> cancelAllSignals ntfnPtr = do
>         stateAssert sch_act_wf_asrt "`sch_act_wf (ksSchedulerAction s) s`"
>         stateAssert ksReadyQueues_asrt ""
>         ntfn <- getNotification ntfnPtr
>         case ntfnState ntfn of
>             Waiting -> do
>                 let q = ntfnQueue ntfn
>                 stateAssert (tcb_queue_head_end_valid_asrt q) ""
>                 whileLoop (\ptrOpt -> const (ptrOpt /= Nothing))
>                           (\ptrOpt -> do
>                                assert (ptrOpt /= Nothing) "the option type must not be Nothing"
>                                ptr <- return $ fromJust ptrOpt
>                                next <- threadGet tcbSchedNext ptr
>                                removeAndRestartNTFNQueuedThread ptr ntfnPtr
>                                return next)
>                           (tcbQueueHead q)
>                 ntfn <- getNotification ntfnPtr
>                 assert (ntfnState ntfn == IdleNtfnState) "the notification must now be idle"
>                 rescheduleRequired
>             _ -> return ()

The following function will remove the given thread from the queue of the notification object, and replace the thread's IPC block with a fault block (which will retry the operation if the thread is resumed).

> cancelSignal :: PPtr TCB -> PPtr Notification -> Kernel ()
> cancelSignal threadPtr ntfnPtr = do
>         stateAssert sym_refs_asrt "`sym_refs (state_refs_of' s)`"
>         stateAssert ready_qs_runnable "threads in the ready queues are runnable'"
>         tcbNTFNDequeue threadPtr ntfnPtr
>         setThreadState Inactive threadPtr

> completeSignal :: PPtr Notification -> PPtr TCB -> Kernel ()
> completeSignal ntfnPtr tcbPtr = do
>         ntfn <- getNotification ntfnPtr
>         case ntfnState ntfn of
>             Active -> do
>                 let badge = fromJust $ ntfnMsgIdentifier ntfn
>                 asUser tcbPtr $ setRegister badgeRegister badge
>                 updateNotification ntfnPtr (\notification -> notification { ntfnState = IdleNtfnState, ntfnMsgIdentifier = Nothing })
>                 maybeDonateSc tcbPtr ntfnPtr
>                 scOpt <- threadGet tcbSchedContext tcbPtr
>                 case scOpt of
>                     Just scp -> do
>                         sc <- getSchedContext scp
>                         when (scSporadic sc) $ do
>                             ntfnScPtr <- liftM ntfnSc $ getNotification ntfnPtr
>                             curScPtr <- getCurSc
>                             when (scOpt == ntfnScPtr && scp /= curScPtr) $ refillUnblockCheck scp
>                     Nothing -> return ()
>             _ -> fail "tried to complete signal with inactive notification object"


\subsection{Accessing Notification Objects}

The following functions are specialisations of the "getObject" and "setObject" for the "Notification" object and pointer type.

> getNotification :: PPtr Notification -> Kernel Notification
> getNotification = getObject

> setNotification :: PPtr Notification -> Notification -> Kernel ()
> setNotification = setObject

> updateNotification :: PPtr Notification -> (Notification -> Notification) -> Kernel ()
> updateNotification ntfnPtr upd = do
>     ntfn <- getNotification ntfnPtr
>     setNotification ntfnPtr (upd ntfn)

\subsection{Miscellaneous}

> bindNotification :: PPtr TCB -> PPtr Notification -> Kernel ()
> bindNotification tcb ntfnPtr = do
>     -- set the bound tcb inside the ntfn
>     updateNotification ntfnPtr (\ntfn -> ntfn { ntfnBoundTCB = Just tcb })
>     -- set the bound ntfn inside the thread
>     setBoundNotification (Just ntfnPtr) tcb

> doUnbindNotification :: PPtr Notification -> PPtr TCB -> Kernel ()
> doUnbindNotification ntfnPtr tcbptr = do
>     updateNotification ntfnPtr (\ntfn -> ntfn { ntfnBoundTCB = Nothing })
>     setBoundNotification Nothing tcbptr

> unbindNotification :: PPtr TCB -> Kernel ()
> unbindNotification tcb = do
>     ntfnPtrOpt <- getBoundNotification tcb
>     case ntfnPtrOpt of
>         Just ntfnPtr -> doUnbindNotification ntfnPtr tcb
>         Nothing -> return ()

> unbindMaybeNotification :: PPtr Notification -> Kernel ()
> unbindMaybeNotification ntfnPtr = do
>     ntfn <- getNotification ntfnPtr
>     case ntfnBoundTCB ntfn of
>         Just t -> doUnbindNotification ntfnPtr t
>         Nothing -> return ()

> ntfnBlocked :: ThreadState -> Maybe (PPtr Notification)
> ntfnBlocked ts = case ts of
>     BlockedOnNotification r -> Just r
>     _ -> Nothing

> tcbNTFNDequeue :: PPtr TCB -> PPtr Notification -> Kernel ()
> tcbNTFNDequeue tcbPtr ntfnPtr = do
>     notification <- getNotification ntfnPtr
>     q' <- tcbQueueRemove (ntfnQueue notification) tcbPtr
>     updateNotification ntfnPtr (\notification -> notification { ntfnQueue = q' })
>     when (tcbQueueEmpty q') $
>         updateNotification ntfnPtr (\notification -> notification { ntfnState = IdleNtfnState, ntfnMsgIdentifier = Nothing })

> tcbNTFNAppend :: PPtr TCB -> PPtr Notification -> Kernel ()
> tcbNTFNAppend tcbPtr ntfnPtr = do
>     notification <- getNotification ntfnPtr
>     stateAssert (tcb_queue_head_end_valid_asrt (ntfnQueue notification)) ""
>     q' <- tcbAppend tcbPtr (ntfnQueue notification)
>     updateNotification ntfnPtr (\notification -> notification { ntfnQueue = q' , ntfnState = Waiting, ntfnMsgIdentifier = Nothing })

> reorderNtfn :: PPtr Notification -> PPtr TCB -> Kernel ()
> reorderNtfn ntfnPtr tptr = do
>     notification <- getNotification ntfnPtr
>     q' <- tcbQueueRemove (ntfnQueue notification) tptr
>     q'' <- tcbAppend tptr q'
>     updateNotification ntfnPtr (\notification -> notification { ntfnQueue = q'' })

> ntfnSetActive :: PPtr Notification -> Word -> Kernel ()
> ntfnSetActive ntfnPtr badge =
>     updateNotification ntfnPtr (\notification -> notification { ntfnState = Active , ntfnMsgIdentifier = Just badge })
