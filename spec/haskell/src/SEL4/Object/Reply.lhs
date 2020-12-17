%
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
% {-# BOOT-EXPORTS: replyRemove replyRemoveTCB replyPush replyUnlink getReply setReply #-}

> import {-# SOURCE #-} SEL4.Kernel.Thread(getThreadState, setThreadState)
> import SEL4.Machine.RegisterSet(PPtr)
> import SEL4.Model.StateData
> import SEL4.Model.PSpace(getObject, setObject)
> import SEL4.Object.SchedContext
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB

> import Data.Maybe(fromJust)

\end{impdetails}


> updateReply :: PPtr Reply -> (Reply -> Reply) -> Kernel ()
> updateReply replyPtr upd = do
>     reply <- getReply replyPtr
>     setReply replyPtr (upd reply)

> replyPush :: PPtr TCB -> PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> replyPush callerPtr calleePtr replyPtr canDonate = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     scPtrOptDonated <- threadGet tcbSchedContext callerPtr
>     tptrOpt <- liftM replyTCB (getReply replyPtr)
>     assert (tptrOpt == Nothing) "Reply object shouldn't have unexecuted reply!"

>     scPtrOptCallee <- threadGet tcbSchedContext calleePtr
>     canDonate <- return (if scPtrOptCallee /= Nothing then False else canDonate)

>     reply <- getReply replyPtr
>     assert (replyPrev reply == Nothing) "replyPush: replyPrev must be Nothing"
>     assert (replyNext reply == Nothing) "replyPush: replyNext must be Nothing"

>     tsCaller <- getThreadState callerPtr
>     assert (replyObject tsCaller == Nothing) "tcb caller should not be in a existing call stack"

>     tsCallee <- getThreadState calleePtr
>     assert (replyObject tsCallee == Nothing) "tcb callee should not be in a existing call stack"

>     updateReply replyPtr (\reply -> reply { replyTCB = Just callerPtr })
>     setThreadState (BlockedOnReply (Just replyPtr)) callerPtr

>     when (scPtrOptDonated /= Nothing && canDonate) $ do
>         assert (scPtrOptCallee == Nothing) "replyPush: callee must not have a scheduling context"

>         scDonated <- getSchedContext (fromJust scPtrOptDonated)
>         oldReplyPtrOpt <- return $ scReply scDonated

>         when (oldReplyPtrOpt /= Nothing) $ do
>             oldReplyPtr <- return $ fromJust oldReplyPtrOpt
>             oldReply <- getReply oldReplyPtr
>             assert (replyNext oldReply == Just (Head $ fromJust scPtrOptDonated))
>                 "replyPush: scheduling context and reply must have reference to each other"

>         reply' <- getReply replyPtr
>         setReply replyPtr (reply' { replyPrev = oldReplyPtrOpt, replyNext = Just (Head $ fromJust scPtrOptDonated) })
>         when (oldReplyPtrOpt /= Nothing) $ do
>             oldReplyPtr <- return $ fromJust oldReplyPtrOpt
>             oldReply <- getReply oldReplyPtr
>             setReply oldReplyPtr (oldReply { replyNext = Just (Next replyPtr) })
>         scDonated <- getSchedContext (fromJust scPtrOptDonated)
>         setSchedContext (fromJust scPtrOptDonated) (scDonated { scReply = Just replyPtr })

>         schedContextDonate (fromJust scPtrOptDonated) calleePtr

> replyPop :: PPtr Reply -> PPtr TCB -> Kernel ()
> replyPop replyPtr tcbPtr = do
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
>         tcbScPtrOpt <- threadGet tcbSchedContext tcbPtr
>         setSchedContext scPtr (sc { scReply = prevReplyPtrOpt })
>         when (prevReplyPtrOpt /= Nothing) $ do
>             prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>             updateReply prevReplyPtr (\reply -> reply { replyNext = replyNext reply })
>         when (tcbScPtrOpt == Nothing) $ schedContextDonate scPtr tcbPtr
>     cleanReply replyPtr
>     replyUnlink replyPtr tcbPtr

> replyRemove :: PPtr Reply -> PPtr TCB -> Kernel ()
> replyRemove replyPtr tcbPtr = do
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

> getReply :: PPtr Reply -> Kernel Reply
> getReply rptr = getObject rptr

> setReply :: PPtr Reply -> Reply -> Kernel ()
> setReply rptr r = setObject rptr r
