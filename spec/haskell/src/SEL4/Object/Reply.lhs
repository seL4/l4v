%
% Copyright 2022, Proofcraft Pty Ltd
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module specifies the behavior of reply objects.

> module SEL4.Object.Reply (
>         replyRemove, replyPush, replyUnlink, getReply, setReply,
>         replyRemoveTCB, updateReply
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: replyRemove replyRemoveTCB replyPush replyUnlink updateReply #-}

> import {-# SOURCE #-} SEL4.Kernel.Thread(getThreadState, setThreadState)
> import SEL4.Machine.RegisterSet(PPtr)
> import SEL4.Model.StateData
> import SEL4.Model.PSpace(getObject, setObject, maybeToMonad)
> import SEL4.Object.SchedContext
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB

> import Data.Maybe(fromJust)

\end{impdetails}

> getReply :: PPtr Reply -> Kernel Reply
> getReply rptr = getObject rptr

> setReply :: PPtr Reply -> Reply -> Kernel ()
> setReply rptr r = setObject rptr r

> updateReply :: PPtr Reply -> (Reply -> Reply) -> Kernel ()
> updateReply replyPtr upd = do
>     reply <- getReply replyPtr
>     setReply replyPtr (upd reply)

> bindScReply :: PPtr SchedContext -> PPtr Reply -> Kernel ()
> bindScReply scPtr replyPtr = do
>     stateAssert sym_refs_asrt
>         "bindScReply: `sym_refs (state_refs_of' s)` must hold"
>     sc <- getSchedContext scPtr
>     scReplyOpt <- return $ scReply sc
>     when (scReplyOpt /= Nothing) $ do
>         scReplyPtr <- return $ fromJust scReplyOpt
>         stateAssert (valid_replies'_sc_asrt scReplyPtr)
>             "Assert that `valid_replies'_sc` holds for replyPtr"
>         updateReply scReplyPtr (\reply -> reply { replyNext = Just (Next replyPtr) })
>     updateReply replyPtr (\reply -> reply { replyPrev = scReplyOpt })
>     setSchedContext scPtr (sc { scReply = Just replyPtr })
>     updateReply replyPtr (\reply -> reply { replyNext = Just (Head $ scPtr) })

> replyPush :: PPtr TCB -> PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> replyPush callerPtr calleePtr replyPtr canDonate = do
>     stateAssert (valid_replies'_sc_asrt replyPtr)
>         "replyPush: valid_replies'_sc holds for replyPtr"
>     stateAssert valid_idle'_asrt
>         "Assert that `valid_idle' s` holds"
>     scPtrOptDonated <- threadGet tcbSchedContext callerPtr
>     scPtrOptCallee <- threadGet tcbSchedContext calleePtr

>     updateReply replyPtr (\reply -> reply { replyTCB = Just callerPtr })
>     setThreadState (BlockedOnReply (Just replyPtr)) callerPtr

>     when (scPtrOptDonated /= Nothing && scPtrOptCallee == Nothing && canDonate) $ do
>         bindScReply (fromJust scPtrOptDonated) replyPtr
>         schedContextDonate (fromJust scPtrOptDonated) calleePtr

> replyPop :: PPtr Reply -> PPtr TCB -> Kernel ()
> replyPop replyPtr tcbPtr = do
>     stateAssert sym_refs_asrt
>         "replyPush: `sym_refs (state_refs_of' s)` must hold"
>     reply <- getReply replyPtr
>     tptr <- maybeToMonad $ replyTCB reply
>     assert (tptr == tcbPtr) "replyPop: replyTCB must be equal to tcbPtr"
>     state <- getThreadState tcbPtr
>     assert (isReply state) "replyPop: thread state must be BlockedOnReply"
>     assert (replyObject state == Just replyPtr) "replyPop: thread state must have replyPtr as its reply"

>     prevReplyPtrOpt <- return $ replyPrev reply
>     nextReplyPtrOpt <- return $ replyNext reply
>     when (nextReplyPtrOpt /= Nothing) $ do
>         assert (isHead nextReplyPtrOpt) "the reply must be at the head"
>         scPtr <- return $ theHeadScPtr nextReplyPtrOpt
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scReply = prevReplyPtrOpt })
>         when (prevReplyPtrOpt /= Nothing) $ do
>             prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>             updateReply prevReplyPtr (\prevReply -> prevReply { replyNext = replyNext reply })
>         updateReply replyPtr (\reply -> reply { replyNext = Nothing })
>         tcbScPtrOpt <- threadGet tcbSchedContext tcbPtr
>         when (tcbScPtrOpt == Nothing) $ schedContextDonate scPtr tcbPtr
>     cleanReply replyPtr
>     replyUnlink replyPtr tcbPtr

> replyRemove :: PPtr Reply -> PPtr TCB -> Kernel ()
> replyRemove replyPtr tcbPtr = do
>     stateAssert sym_refs_asrt
>         "replyRemove: `sym_refs (state_refs_of' s)` must hold"
>     reply <- getReply replyPtr
>     tptr <- maybeToMonad  $ replyTCB reply
>     assert (tptr == tcbPtr) "replyRemove: replyTCB must be equal to tcbPtr"
>     state <- getThreadState tcbPtr
>     assert (isReply state) "replyRemove: thread state must be BlockedOnReply"
>     assert (replyObject state == Just replyPtr) "replyRemove: thread state must have replyPtr as its reply"

>     nextReplyPtrOpt <- return $ replyNext reply
>     prevReplyPtrOpt <- return $ replyPrev reply
>     if nextReplyPtrOpt /= Nothing && isHead nextReplyPtrOpt
>        then replyPop replyPtr tcbPtr
>        else do
>            when (nextReplyPtrOpt /= Nothing) $ do
>                nextReplyPtr <- return $ theReplyNextPtr nextReplyPtrOpt
>                updateReply nextReplyPtr (\reply -> reply { replyPrev = Nothing })

>            when (prevReplyPtrOpt /= Nothing) $ do
>                prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>                updateReply prevReplyPtr (\reply -> reply { replyNext = Nothing })

>            cleanReply replyPtr
>            replyUnlink replyPtr tcbPtr

> replyRemoveTCB :: PPtr TCB -> Kernel ()
> replyRemoveTCB tptr = do
>     state <- getThreadState tptr
>     assert (isReply state) "replyRemoveTCB: thread state must be BlockedOnReply"

>     rptr <- maybeToMonad $ replyObject state
>     reply <- getReply rptr
>     nextReplyPtrOpt <- return $ replyNext reply
>     prevReplyPtrOpt <- return $ replyPrev reply

>     when (nextReplyPtrOpt /= Nothing) $ do
>        if isHead nextReplyPtrOpt
>            then do
>               scPtr <- return $ theHeadScPtr nextReplyPtrOpt
>               sc <- getSchedContext scPtr
>               setSchedContext scPtr (sc { scReply = Nothing })
>            else do
>               nextReplyPtr <- return $ theReplyNextPtr nextReplyPtrOpt
>               updateReply nextReplyPtr (\reply -> reply { replyPrev = Nothing })

>     when (prevReplyPtrOpt /= Nothing) $ do
>         prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>         updateReply prevReplyPtr (\reply -> reply { replyNext = Nothing })

>     cleanReply rptr
>     replyUnlink rptr tptr

> replyUnlink :: PPtr Reply -> PPtr TCB -> Kernel ()
> replyUnlink replyPtr tcbPtr = do
>     tptrOpt <- liftM replyTCB (getReply replyPtr)
>     tptr <- maybeToMonad tptrOpt
>     assert (tptr == tcbPtr) "replyTCB must be equal to tcbPtr"
>     state <- getThreadState tcbPtr
>     stateAssert (replyUnlink_assertion replyPtr state)
>             "Relation between the thread state of the replyTCB and replyPtr"
>     updateReply replyPtr (\reply -> reply { replyTCB = Nothing })
>     setThreadState Inactive tcbPtr

In "replyUnlink" above, as in the abstract specification,  we make an assertion
on the thread state of the replyTCB of the replyPtr

> replyUnlink_assertion :: PPtr Reply -> ThreadState -> KernelState -> Bool
> replyUnlink_assertion _ _ _ = True

> cleanReply :: PPtr Reply -> Kernel ()
> cleanReply replyPtr = do
>     updateReply replyPtr $ \reply -> reply { replyPrev = Nothing }
>     updateReply replyPtr $ \reply -> reply { replyNext = Nothing }
