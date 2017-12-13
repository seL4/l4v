%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
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
>         schedContextDonate scPtr tcbPtr
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
>     assert (isReply state)
>         "replyRemove: thread state must be BlockedOnReply"
>     nextReplyPtrOpt <- return $ replyNext reply
>     scPtrOpt <- return $ replySc reply

>     if scPtrOpt /= Nothing
>         then replyPop replyPtr
>         else if nextReplyPtrOpt /= Nothing
>                  then do
>                      setPrevOfNextReply replyPtr
>                      let nextReplyPtr = fromJust nextReplyPtrOpt
>                      tcbPtrOptNext <- getReplyTCB nextReplyPtr
>                      when (tcbPtrOptNext /= Nothing) $
>                          replyUnlink nextReplyPtr
>                      setReplyTCB tcbPtrOpt nextReplyPtr
>                      setReplyTCB Nothing replyPtr
>                      setThreadState (BlockedOnReply $ Just nextReplyPtr) (fromJust tcbPtrOpt)
>                      setNextOfPrevReply replyPtr
>                      cleanReply replyPtr
>                  else do
>                      when (tcbPtrOpt /= Nothing) $
>                          replyUnlink replyPtr
>                      setNextOfPrevReply replyPtr
>                      cleanReply replyPtr

> replyPush :: PPtr TCB -> PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> replyPush callerPtr calleePtr replyPtr canDonate = do
>     scPtrOptDonated <- threadGet tcbSchedContext callerPtr
>     tptrOpt <- getReplyTCB replyPtr
>     assert (tptrOpt == Nothing) "Reply object shouldn't have unexecuted reply!"

>     scPtrOptCallee <- threadGet tcbSchedContext calleePtr
>     canDonate <- return (if scPtrOptCallee /= Nothing then False else canDonate)

>     reply <- getReply replyPtr
>     assert (replyPrev reply == Nothing) "replyPush: replyPrev must be Nothing"
>     assert (replyNext reply == Nothing &&
>             replySc reply == Nothing) "replyPush: both replyNext and replySc must be Nothing"

>     tsCaller <- getThreadState callerPtr
>     assert ((not (isReceive tsCaller || isReply tsCaller)) ||
>             replyObject tsCaller == Nothing) "tcb caller should not be in a existing call stack"

>     tsCallee <- getThreadState calleePtr
>     when (isReceive tsCallee || isReply tsCallee) $
>         setThreadState tsCallee { replyObject = Nothing } calleePtr

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

> replyUnlink :: PPtr Reply -> Kernel ()
> replyUnlink rptr = do
>     tptrOpt <- getReplyTCB rptr
>     setReplyTCB Nothing rptr
>     setThreadState Inactive $ fromJust tptrOpt

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
>         then replyPop rptr
>         else do
>             setPrevOfNextReply $ rptr
>             setNextOfPrevReply $ rptr
>             cleanReply rptr
>             replyUnlink rptr

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

> setPrevOfNextReply :: PPtr Reply -> Kernel ()
> setPrevOfNextReply replyPtr = do
>     reply <- getReply replyPtr
>     nextReplyPtrOpt <- return $ replyNext reply
>     when (nextReplyPtrOpt /= Nothing) $ do
>         nextReplyPtr <- return $ fromJust nextReplyPtrOpt
>         nextReply <- getReply nextReplyPtr
>         setReply nextReplyPtr (nextReply { replyPrev = replyPrev reply })

> setNextOfPrevReply :: PPtr Reply -> Kernel ()
> setNextOfPrevReply replyPtr = do
>     reply <- getReply replyPtr
>     prevReplyPtrOpt <- return $ replyPrev reply
>     when (prevReplyPtrOpt /= Nothing) $ do
>         prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>         prevReply <- getReply prevReplyPtr
>         setReply prevReplyPtr (prevReply { replyNext = replyNext reply, replySc = replySc reply })
>
> cleanReply :: PPtr Reply -> Kernel ()
> cleanReply replyPtr = do
>     reply <- getReply replyPtr
>     setReply replyPtr (reply { replyPrev = Nothing, replyNext = Nothing, replySc = Nothing })

> replyClear :: PPtr Reply -> Kernel ()
> replyClear rptr = do
>     tptrOpt <- getReplyTCB rptr
>     assert (tptrOpt /= Nothing) "replyClear: TCB pointer should not be nothing."
>     state <- getThreadState $ fromJust tptrOpt
>     case state of
>         BlockedOnReply _ -> replyRemove rptr
>         BlockedOnReceive {} -> replyUnlink rptr
>         _ -> fail "replyClear: invalid state of replyTCB"

