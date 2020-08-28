%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module specifies the behavior of notification objects.

> module SEL4.Object.Notification (
>         sendSignal, receiveSignal,
>         cancelAllSignals, cancelSignal, completeSignal,
>         getNotification, setNotification, doUnbindNotification, unbindNotification,
>         unbindMaybeNotification, bindNotification, doNBRecvFailedTransfer,
>         ntfnBlocked, reorderNtfn
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: getNotification setNotification #-}

> import Prelude hiding (Word)
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.Endpoint(cancelIPC)
> import SEL4.Object.SchedContext
> import {-# SOURCE #-} SEL4.Object.TCB
> import SEL4.Object.Instances()

> import {-# SOURCE #-} SEL4.Kernel.Thread

> import Data.Bits
> import Data.List
> import Data.Maybe(fromJust)

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

>         nTFN <- getNotification ntfnPtr
>         case (ntfnObj nTFN, ntfnBoundTCB nTFN) of

If the notification object is idle, store the badge and the value, and then
mark the notification object as active.

>             (IdleNtfn, Just tcb) -> do
>                     state <- getThreadState tcb
>                     if (receiveBlocked state)
>                       then do
>                         cancelIPC tcb
>                         setThreadState Running tcb
>                         asUser tcb $ setRegister badgeRegister badge
>                         maybeDonateSc tcb ntfnPtr
>                         schedulable <- isSchedulable tcb
>                         when schedulable $ possibleSwitchTo tcb
>                       else
>                         setNotification ntfnPtr $ nTFN { ntfnObj = ActiveNtfn badge }
>             (IdleNtfn, Nothing) -> setNotification ntfnPtr $ nTFN { ntfnObj = ActiveNtfn badge }

If the notification object is waiting, a thread is removed from its queue and the signal is transferred to it.

>             (WaitingNtfn (dest:queue), _) -> do
>                 setNotification ntfnPtr $ nTFN {
>                   ntfnObj = case queue of
>                     [] -> IdleNtfn
>                     _  -> WaitingNtfn queue
>                   }
>                 setThreadState Running dest
>                 asUser dest $ setRegister badgeRegister badge
>                 maybeDonateSc dest ntfnPtr
>                 schedulable <- isSchedulable dest
>                 when schedulable $ possibleSwitchTo dest
>             (WaitingNtfn [], _) -> fail "WaitingNtfn Notification must have non-empty queue"

If the notification object is active, new values are calculated and stored in the notification object. The calculation is done by a bitwise OR operation of the currently stored, and the newly sent values.

>             (ActiveNtfn badge', _) -> do
>                 let newBadge = badge .|. badge'
>                 setNotification ntfnPtr $ nTFN { ntfnObj = ActiveNtfn newBadge }

\subsection{Receiving Signals}

This function performs an receive signal operation, given a thread pointer and a capability to a notification object. The receive can be either blocking (the thread will be blocked on the notification until a signal arrives) or non-blocking depending on the isBlocking flag.

> doNBRecvFailedTransfer :: PPtr TCB -> Kernel ()
> doNBRecvFailedTransfer thread = asUser thread $ setRegister badgeRegister 0


> receiveSignal :: PPtr TCB -> Capability -> Bool -> Kernel ()

> receiveSignal thread cap isBlocking = do

Fetch the notification object, and select the operation based on its state.

>         let ntfnPtr = capNtfnPtr cap
>         ntfn <- getNotification ntfnPtr
>         case ntfnObj ntfn of

If the notification object is idle, then it becomes a waiting notification object, with the current thread in its queue. The thread is blocked.

>             IdleNtfn -> case isBlocking of
>                 True -> do
>                       setThreadState (BlockedOnNotification {
>                                          waitingOnNotification = ntfnPtr } ) thread
>                       maybeReturnSc ntfnPtr thread
>                       scheduleTCB thread
>                       setNotification ntfnPtr $ ntfn {ntfnObj = WaitingNtfn ([thread]) }
>                 False -> doNBRecvFailedTransfer thread

If the notification object is already waiting, the current thread is blocked and added to the queue. Note that this case cannot occur when the notification object is bound, as only the associated thread can wait on it.

>             WaitingNtfn queue -> case isBlocking of
>                 True -> do
>                       setThreadState (BlockedOnNotification {
>                                          waitingOnNotification = ntfnPtr } ) thread
>                       maybeReturnSc ntfnPtr thread
>                       scheduleTCB thread
>                       qs' <- tcbEPAppend thread queue
>                       setNotification ntfnPtr $ ntfn {ntfnObj = WaitingNtfn qs' }
>                 False -> doNBRecvFailedTransfer thread

If the notification object is active, the badge of the invoked notification object capability will be loaded to the badge of the receiving thread and the notification object will be marked as idle.

>             ActiveNtfn badge -> do
>                 asUser thread $ setRegister badgeRegister badge
>                 setNotification ntfnPtr $ ntfn {ntfnObj = IdleNtfn }
>                 maybeDonateSc thread ntfnPtr

\subsection{Delete Operation}

If a notification object is deleted, then pending receive operations must be cancelled.

> cancelAllSignals :: PPtr Notification -> Kernel ()
> cancelAllSignals ntfnPtr = do
>         stateAssert sym_refs_asrt
>             "Assert that `sym_refs (state_refs_of' s)` holds"
>         ntfn <- getNotification ntfnPtr
>         case ntfnObj ntfn of
>             WaitingNtfn queue -> do
>                 setNotification ntfnPtr (ntfn { ntfnObj = IdleNtfn })
>                 forM_ queue (\t -> do
>                     setThreadState Restart t
>                     possibleSwitchTo t)
>                 rescheduleRequired
>             _ -> return ()

The following function will remove the given thread from the queue of the notification object, and replace the thread's IPC block with a fault block (which will retry the operation if the thread is resumed).

> cancelSignal :: PPtr TCB -> PPtr Notification -> Kernel ()
> cancelSignal threadPtr ntfnPtr = do
>         ntfn <- getNotification ntfnPtr
>         assert (isWaiting (ntfnObj ntfn))
>             "cancelSignal: notification object must be waiting"
>         let queue' = delete threadPtr $ ntfnQueue $ ntfnObj ntfn
>         ntfn' <- case queue' of
>             [] -> return $ IdleNtfn
>             _ -> return $ (ntfnObj ntfn) { ntfnQueue = queue' }
>         setNotification ntfnPtr (ntfn { ntfnObj = ntfn' })
>         setThreadState Inactive threadPtr
>     where
>       isWaiting ntfn = case ntfn of
>                       WaitingNtfn {} -> True
>                       _ -> False

> completeSignal :: PPtr Notification -> PPtr TCB -> Kernel ()
> completeSignal ntfnPtr tcb = do
>         ntfn <- getNotification ntfnPtr
>         case ntfnObj ntfn of
>             ActiveNtfn badge -> do
>                 asUser tcb $ setRegister badgeRegister badge
>                 setNotification ntfnPtr $ ntfn {ntfnObj = IdleNtfn}
>             _ -> fail "tried to complete signal with inactive notification object"


\subsection{Accessing Notification Objects}

The following functions are specialisations of the "getObject" and "setObject" for the "Notification" object and pointer type.

> getNotification :: PPtr Notification -> Kernel Notification
> getNotification = getObject

> setNotification :: PPtr Notification -> Notification -> Kernel ()
> setNotification = setObject


\subsection{Miscellaneous}

> bindNotification :: PPtr TCB -> PPtr Notification -> Kernel ()
> bindNotification tcb ntfnPtr = do
>     -- set the bound tcb inside the ntfn
>     ntfn <- getNotification ntfnPtr
>     setNotification ntfnPtr $ ntfn { ntfnBoundTCB = Just tcb }
>     -- set the bound ntfn inside the thread
>     setBoundNotification (Just ntfnPtr) tcb

> doUnbindNotification :: PPtr Notification -> Notification -> PPtr TCB -> Kernel ()
> doUnbindNotification ntfnPtr ntfn tcbptr = do
>     let ntfn' = ntfn { ntfnBoundTCB = Nothing }
>     setNotification ntfnPtr ntfn'
>     setBoundNotification Nothing tcbptr

> unbindNotification :: PPtr TCB -> Kernel ()
> unbindNotification tcb = do
>     ntfnPtr <- getBoundNotification tcb
>     case ntfnPtr of
>         Just ntfnPtr' -> do
>              ntfn <- getNotification ntfnPtr'
>              doUnbindNotification ntfnPtr' ntfn tcb
>         Nothing -> return ()

> unbindMaybeNotification :: PPtr Notification -> Kernel ()
> unbindMaybeNotification ntfnPtr = do
>     ntfn <- getNotification ntfnPtr
>     case ntfnBoundTCB ntfn of
>         Just t -> doUnbindNotification ntfnPtr ntfn t
>         Nothing -> return ()

> ntfnBlocked :: ThreadState -> Maybe (PPtr Notification)
> ntfnBlocked ts = case ts of
>     BlockedOnNotification r -> Just r
>     _ -> Nothing

> reorderNtfn :: PPtr Notification -> PPtr TCB -> Kernel ()
> reorderNtfn ntfnPtr tptr = do
>     ntfn <- getNotification ntfnPtr
>     qsOpt <- return $ getntfnQueue ntfn
>     assert (qsOpt /= Nothing) "reorder_ntfn: the notification queue must not be Nothing"
>     qs <- return $ fromJust qsOpt
>     qs' <- tcbEPDequeue tptr qs
>     qs'' <- tcbEPAppend tptr qs'
>     setNotification ntfnPtr (ntfn { ntfnObj = WaitingNtfn qs'' })

> getntfnQueue :: Notification -> Maybe [PPtr TCB]
> getntfnQueue ntfn =
>     case ntfnObj ntfn of
>         WaitingNtfn qs -> Just qs
>         _ -> Nothing

