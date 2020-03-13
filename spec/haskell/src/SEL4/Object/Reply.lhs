%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module specifies the behavior of reply objects.

> module SEL4.Object.Reply (
>         replyClear, replyRemove, replyPush, replyUnlink, getReply, setReply, getReplyTCB,
>         replyRemoveTCB, setReplyTCB
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: replyClear replyRemove replyRemoveTCB replyPush replyUnlink getReply setReply getReplyTCB #-}

> import {-# SOURCE #-} SEL4.Kernel.Thread(getThreadState, setThreadState)
> import SEL4.Machine.RegisterSet(PPtr)
> import SEL4.Model.StateData
> import SEL4.Model.PSpace(getObject, setObject)
> import SEL4.Object.SchedContext
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB

> import Data.Maybe(fromJust)

\end{impdetails}

> replyPush :: PPtr TCB -> PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> replyPush callerPtr calleePtr replyPtr canDonate = do
>     scPtrOptDonated <- threadGet tcbSchedContext callerPtr
>     tptrOpt <- getReplyTCB replyPtr
>     assert (tptrOpt == Nothing) "Reply object shouldn't have unexecuted reply!"

>     scPtrOptCallee <- threadGet tcbSchedContext calleePtr
>     canDonate <- return (if scPtrOptCallee /= Nothing then False else canDonate)

>     reply <- getReply replyPtr
>     assert (replyPrev reply == Nothing) "replyPush: replyPrev must be Nothing"
>     assert (replyNext reply == Nothing) "replyPush: replyNext must be Nothing"

>     tsCaller <- getThreadState callerPtr
>     assert (replyObject tsCaller == Nothing) "tcb caller should not be in a existing call stack"

>     tsCallee <- getThreadState calleePtr
>     setThreadState tsCallee { replyObject = Nothing } calleePtr

>     setReplyTCB (Just callerPtr) replyPtr
>     setThreadState (BlockedOnReply (Just replyPtr)) callerPtr

>     when (scPtrOptDonated /= Nothing && canDonate) $ do
>         assert (scPtrOptCallee == Nothing) "replyPush: callee must not have a scheduling context"

>         scDonated <- getSchedContext (fromJust scPtrOptDonated)
>         oldReplyPtrOpt <- return $ scReply scDonated

>         when (oldReplyPtrOpt /= Nothing) $ do
>             oldReplyPtr <- return $ fromJust oldReplyPtrOpt
>             oldReply <- getReply oldReplyPtr
>             assert (replySc oldReply == scPtrOptDonated)
>                 "replyPush: scheduling context and reply must have reference to each other"

>         reply' <- getReply replyPtr
>         setReply replyPtr (reply' { replyPrev = oldReplyPtrOpt, replyNext = Nothing,
>                                     replySc = scPtrOptDonated })
>         when (oldReplyPtrOpt /= Nothing) $ do
>             oldReplyPtr <- return $ fromJust oldReplyPtrOpt
>             oldReply <- getReply oldReplyPtr
>             setReply oldReplyPtr (oldReply { replyNext = Just replyPtr, replySc = Nothing })
>         scDonated <- getSchedContext (fromJust scPtrOptDonated)
>         setSchedContext (fromJust scPtrOptDonated) (scDonated { scReply = Just replyPtr })

>         schedContextDonate (fromJust scPtrOptDonated) calleePtr

> replyPop :: PPtr Reply -> Kernel ()
> replyPop replyPtr = do
>     reply <- getReply replyPtr
>     tcbPtrOpt <- return $ replyTCB reply
>     assert (tcbPtrOpt /= Nothing) "replyPop: replyTCB must not be Nothing"

>     tcbPtr <- return $ fromJust tcbPtrOpt
>     state <- getThreadState tcbPtr
>     assert (isReply state) "replyPop: thread state must be BlockedOnReply"

>     replyUnlink replyPtr

>     prevReplyPtrOpt <- return $ replyPrev reply
>     scPtrOpt <- return $ replySc reply
>     when (scPtrOpt /= Nothing) $ do
>         scPtr <- return $ fromJust scPtrOpt
>         tcbScPtrOpt <- threadGet tcbSchedContext tcbPtr
>         when (tcbScPtrOpt == Nothing) $ schedContextDonate scPtr tcbPtr
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scReply = prevReplyPtrOpt })
>         when (prevReplyPtrOpt /= Nothing) $ do
>             prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>             prevReply <- getReply prevReplyPtr
>             setReply prevReplyPtr (prevReply { replyNext = replyNext reply })
>         cleanReply replyPtr

> replyRemove :: PPtr Reply -> Kernel ()
> replyRemove replyPtr = do
>     reply <- getReply replyPtr
>     tcbPtrOpt <- return $ replyTCB reply
>     state <- getThreadState $ fromJust tcbPtrOpt
>     assert (isReply state) "replyRemove: thread state must be BlockedOnReply"

>     nextReplyPtrOpt <- return $ replyNext reply
>     prevReplyPtrOpt <- return $ replyPrev reply
>     scPtrOpt <- return $ replySc reply
>     if scPtrOpt /= Nothing
>         then replyPop replyPtr
>         else if nextReplyPtrOpt /= Nothing
>             then do
>                 nextReplyPtr <- return $ fromJust nextReplyPtrOpt
>                 nextReply <- getReply nextReplyPtr
>                 setReply nextReplyPtr (nextReply { replyPrev = Nothing })
>                 replyUnlink replyPtr
>             else when (tcbPtrOpt /= Nothing) $ replyUnlink replyPtr

>     when (prevReplyPtrOpt /= Nothing) $ do
>         prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>         prevReply <- getReply prevReplyPtr
>         setReply prevReplyPtr (prevReply { replyNext = Nothing })

>     cleanReply replyPtr


> replyRemoveTCB :: PPtr TCB -> Kernel ()
> replyRemoveTCB tptr = do
>     state <- getThreadState tptr
>     assert (isReply state) "replyRemoveTCB: thread state must be BlockedOnReply"

>     rptr <- return $ fromJust $ replyObject state
>     reply <- getReply rptr
>     nextReplyPtrOpt <- return $ replyNext reply
>     prevReplyPtrOpt <- return $ replyPrev reply
>     scPtrOpt <- return $ replySc reply

>     if scPtrOpt /= Nothing
>         then do
>             scPtr <- return $ fromJust scPtrOpt
>             sc <- getSchedContext scPtr
>             setSchedContext scPtr (sc { scReply = Nothing })
>         else when (nextReplyPtrOpt /= Nothing) $ do
>             nextReplyPtr <- return $ fromJust nextReplyPtrOpt
>             nextReply <- getReply nextReplyPtr
>             setReply nextReplyPtr (nextReply { replyPrev = Nothing })

>     when (prevReplyPtrOpt /= Nothing) $ do
>         prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>         prevReply <- getReply prevReplyPtr
>         setReply prevReplyPtr (prevReply { replyNext = Nothing })

>     cleanReply rptr
>     replyUnlink rptr

> replyUnlink :: PPtr Reply -> Kernel ()
> replyUnlink replyPtr = do
>     tptrOpt <- getReplyTCB replyPtr
>     let tptr = fromJust tptrOpt
>     state <- getThreadState tptr
>     setThreadState state { replyObject = Nothing } tptr
>     setReplyTCB Nothing replyPtr
>     setThreadState Inactive $ fromJust tptrOpt

> cleanReply :: PPtr Reply -> Kernel ()
> cleanReply replyPtr = do
>     reply <- getReply replyPtr
>     setReply replyPtr (reply { replyPrev = Nothing, replyNext = Nothing, replySc = Nothing })

> getReply :: PPtr Reply -> Kernel Reply
> getReply rptr = getObject rptr

> setReply :: PPtr Reply -> Reply -> Kernel ()
> setReply rptr r = setObject rptr r

> getReplyTCB :: PPtr Reply -> Kernel (Maybe (PPtr TCB))
> getReplyTCB r = liftM replyTCB (getReply r)

> setReplyTCB :: Maybe (PPtr TCB) -> PPtr Reply -> Kernel ()
> setReplyTCB tptrOpt rptr = do
>     r <- getReply rptr
>     setReply rptr r { replyTCB = tptrOpt}

> replyClear :: PPtr Reply -> Kernel ()
> replyClear rptr = do
>     tptrOpt <- getReplyTCB rptr
>     assert (tptrOpt /= Nothing) "replyClear: TCB pointer should not be nothing."
>     state <- getThreadState $ fromJust tptrOpt
>     case state of
>         BlockedOnReply _ -> replyRemove rptr
>         BlockedOnReceive {} -> replyUnlink rptr
>         _ -> fail "replyClear: invalid state of replyTCB"

