%
% Copyright 2022, Proofcraft Pty Ltd
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module specifies the behavior of reply objects.

> module SEL4.Object.Reply (
>         replyRemove, replyLinkCaller, replyUnlink, getReply, setReply,
>         replyRemoveTCB, updateReply
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: replyRemove replyRemoveTCB replyLinkCaller replyUnlink updateReply #-}

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

> replyPush' :: PPtr SchedContext -> PPtr Reply -> Maybe (PPtr Reply) -> Kernel ()
> replyPush' scPtr replyPtr scReplyOpt = do
>     stateAssert (replyPush'_asrt scReplyOpt) ""
>     updateReply replyPtr (\reply -> reply { replyNext = Nothing })
>     updateReply replyPtr (\reply -> reply { replyPrev = scReplyOpt })
>     when (scReplyOpt /= Nothing) $ do
>         scReplyPtr <- return $ fromJust scReplyOpt
>         updateReply scReplyPtr (\reply -> reply { replyNext = Just replyPtr })
>     updateSchedContext scPtr (\sc -> sc { scReply = Just replyPtr })

> replyPush :: PPtr SchedContext -> PPtr Reply -> Kernel ()
> replyPush scPtr replyPtr = do
>     stateAssert sym_refs_asrt "`sym_refs (state_refs_of' s)`"
>     sc <- getSchedContext scPtr
>     scReplyOpt <- return $ scReply sc
>     stateAssert (valid_bound_reply'_asrt scReplyOpt) ""
>     when (scReplyOpt /= Nothing) $ do
>         scReplyPtr <- return $ fromJust scReplyOpt
>         updateReply scReplyPtr (\reply -> reply { replySC = Nothing })
>     replyPush' scPtr replyPtr scReplyOpt
>     updateReply replyPtr (\reply -> reply { replySC = Just scPtr })

> replyLinkCaller :: PPtr TCB -> PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> replyLinkCaller callerPtr calleePtr replyPtr canDonate = do
>     stateAssert valid_idle'_asrt "`valid_idle'`"
>     stateAssert valid_objs'_asrt "`valid_objs'`"
>     stateAssert (not_sched_linked_asrt callerPtr) ""
>     reply <- getReply replyPtr
>     assert (replyTCB reply == Nothing) "the reply must not be linked to a TCB"
>     stateAssert (reply_object_asrt callerPtr) ""
>     scPtrOptDonated <- threadGet tcbSchedContext callerPtr
>     scPtrOptCallee <- threadGet tcbSchedContext calleePtr

>     updateReply replyPtr (\reply -> reply { replyTCB = Just callerPtr })
>     setThreadState (BlockedOnReply (Just replyPtr)) callerPtr

>     when (scPtrOptDonated /= Nothing && scPtrOptCallee == Nothing && canDonate) $ do
>         replyPush (fromJust scPtrOptDonated) replyPtr
>         schedContextDonate (fromJust scPtrOptDonated) calleePtr

> breakReplyChainAt' :: PPtr Reply -> Kernel ()
> breakReplyChainAt' replyPtr = do
>     reply <- getReply replyPtr
>     replyPrevOpt <- return $ replyPrev reply
>     when (replyPrevOpt /= Nothing) $
>         updateReply (fromJust replyPrevOpt) (\reply -> reply { replyNext = Nothing })
>     replyNextOpt <- return $ replyNext reply
>     when (replyNextOpt /= Nothing) $
>         updateReply (fromJust replyNextOpt) (\reply -> reply { replyPrev = Nothing })
>     updateReply replyPtr (\reply -> reply { replyPrev = Nothing })
>     updateReply replyPtr (\reply -> reply { replyNext = Nothing })
>     replySCOpt <- return $ replySC reply
>     when (replySCOpt /= Nothing) $ 
>         updateSchedContext (fromJust replySCOpt) (\sc -> sc { scReply = Nothing })

> breakReplyChainAt :: PPtr Reply -> Kernel ()
> breakReplyChainAt replyPtr = do
>     reply <- getReply replyPtr
>     breakReplyChainAt' replyPtr
>     replySCOpt <- return $ replySC reply
>     when (replySCOpt /= Nothing) $ 
>         updateReply replyPtr (\reply -> reply { replySC = Nothing })

> replyPop' :: PPtr Reply -> PPtr SchedContext -> Maybe (PPtr Reply) -> Kernel ()
> replyPop' replyPtr scPtr prevReplyOpt = do
>     stateAssert (replyPop'_asrt replyPtr scPtr) ""
>     updateReply replyPtr (\reply -> reply { replyPrev = Nothing })
>     when (prevReplyOpt /= Nothing) $ do
>         prevReplyPtr <- return $ fromJust prevReplyOpt
>         updateReply prevReplyPtr (\reply -> reply { replyNext = Nothing })
>     updateSchedContext scPtr (\sc -> sc { scReply = prevReplyOpt })

> replyPop :: PPtr Reply -> Kernel ()
> replyPop replyPtr = do
>     reply <- getReply replyPtr
>     replySCOpt <- return $ replySC reply
>     assert (replySCOpt /= Nothing) "the reply must be the head of the reply stack of some scheduling context"
>     scPtr <- return $ fromJust replySCOpt
>     prevReplyOpt <- return $ replyPrev reply
>     updateReply replyPtr (\reply -> reply { replySC = Nothing })
>     replyPop' replyPtr scPtr prevReplyOpt
>     when (prevReplyOpt /= Nothing) $ do
>         prevPtr <- return $ fromJust prevReplyOpt
>         assert (prevPtr /= replyPtr) "the reply stack must be distinct"
>         updateReply prevPtr (\reply -> reply { replySC = Just scPtr })

> replyRemove :: PPtr Reply -> PPtr TCB -> Kernel ()
> replyRemove replyPtr tcbPtr = do
>     stateAssert sym_refs_asrt "`sym_refs (state_refs_of' s)`"
>     reply <- getReply replyPtr
>     tptr <- maybeToMonad  $ replyTCB reply
>     assert (tptr == tcbPtr) "replyRemove: replyTCB must be equal to tcbPtr"
>     state <- getThreadState tcbPtr
>     assert (isReply state) "replyRemove: thread state must be BlockedOnReply"
>     assert (replyObject state == Just replyPtr) "replyRemove: thread state must have replyPtr as its reply"

>     replySCOpt <- return $ replySC reply
>     case replySCOpt of
>         Nothing -> breakReplyChainAt replyPtr
>         Just scPtr -> do
>             replyPop replyPtr
>             tcbScPtrOpt <- threadGet tcbSchedContext tcbPtr
>             when (tcbScPtrOpt == Nothing) $ schedContextDonate scPtr tcbPtr
>     replyUnlink replyPtr tcbPtr

> replyRemoveTCB :: PPtr TCB -> Kernel ()
> replyRemoveTCB tptr = do
>     stateAssert valid_objs'_asrt "`valid_objs'`"
>     state <- getThreadState tptr
>     assert (isReply state) "replyRemoveTCB: thread state must be BlockedOnReply"
>     rptr <- maybeToMonad $ replyObject state
>     breakReplyChainAt rptr
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
