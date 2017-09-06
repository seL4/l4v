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
>         replyRemove, replyPush, getReply, setReply, getReplyCaller
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: replyRemove replyPush getReply setReply getReplyCaller #-}

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
>     tcbPtrOpt <- return $ replyCaller reply
>     tcbPtr <- return $ fromJust tcbPtrOpt
>     assert (tcbPtrOpt /= Nothing) "replyPop: replyCaller must not be Nothing"
>     setReply replyPtr (reply { replyCaller = Nothing })
>     threadSet (\tcb -> tcb { tcbReply = Nothing }) tcbPtr
>     nextReplyPtrOpt <- return $ replyNext reply
>     prevReplyPtrOpt <- return $ replyPrev reply
>     when (replySc reply /= Nothing || nextReplyPtrOpt /= Nothing) $ do
>         assert (nextReplyPtrOpt == Nothing && replySc reply /= Nothing) "replyPop: reply must be the head of the call stack"
>         nextReplyPtr <- return $ fromJust nextReplyPtrOpt
>         nextReply <- getReply nextReplyPtr
>         scPtr <- return $ fromJust $ replySc nextReply
>         schedContextDonate scPtr tcbPtr
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scReply = prevReplyPtrOpt })
>         when (prevReplyPtrOpt /= Nothing) $ do
>             prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>             prevReply <- getReply prevReplyPtr
>             setReply prevReplyPtr (prevReply { replyNext = replyNext reply })
>         reply' <- getReply replyPtr
>         setReply replyPtr (reply' { replyPrev = Nothing, replyNext = Nothing, replySc = Nothing })

> replyRemove :: PPtr Reply -> Kernel ()
> replyRemove replyPtr = do
>     reply <- getReply replyPtr
>     nextReplyPtrOpt <- return $ replyNext reply
>     scPtrOpt <- return $ replySc reply
>     if scPtrOpt /= Nothing || nextReplyPtrOpt /= Nothing
>         then if nextReplyPtrOpt == Nothing && scPtrOpt /= Nothing
>                  then replyPop replyPtr
>                  else do
>                      nextReplyPtr <- return $ fromJust nextReplyPtrOpt
>                      nextReply <- getReply nextReplyPtr
>                      setReply nextReplyPtr (nextReply { replyPrev = replyPrev reply,
>                                                         replyCaller = replyCaller reply })
>                      tcbPtrOpt <- return $ replyCaller reply
>                      when (tcbPtrOpt /= Nothing) $ do
>                          tcbPtr <- return $ fromJust tcbPtrOpt
>                          threadSet (\tcb -> tcb { tcbReply = Just nextReplyPtr }) tcbPtr
>                          setReply replyPtr (reply { replyCaller = Nothing })
>                      setPrevReply replyPtr
>                      cleanReply replyPtr
>         else do
>             tcbPtrOpt <- return $ replyCaller reply
>             when (tcbPtrOpt /= Nothing) $ do
>                 tcbPtr <- return $ fromJust tcbPtrOpt
>                 threadSet (\tcb -> tcb { tcbReply = Nothing }) tcbPtr
>                 setReply replyPtr (reply { replyCaller = Nothing })
>             setPrevReply replyPtr
>             cleanReply replyPtr

>     where setPrevReply replyPtr = do
>               reply <- getReply replyPtr
>               prevReplyPtrOpt <- return $ replyPrev reply
>               when (prevReplyPtrOpt /= Nothing) $ do
>                   prevReplyPtr <- return $ fromJust prevReplyPtrOpt
>                   prevReply <- getReply prevReplyPtr
>                   setReply prevReplyPtr (prevReply { replyNext = replyNext reply })

>           cleanReply replyPtr = do
>             reply <- getReply replyPtr
>             setReply replyPtr (reply { replyPrev = Nothing, replyNext = Nothing, replySc = Nothing })

> replyPush :: PPtr TCB -> PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> replyPush callerPtr calleePtr replyPtr canDonate = do
>     scPtrOpt <- threadGet tcbSchedContext callerPtr
>     replyCallerPtrOpt <- getReplyCaller replyPtr
>     when (replyCallerPtrOpt /= Nothing) $ replyRemove replyPtr

>     scPtrOpt' <- threadGet tcbSchedContext calleePtr
>     canDonate <- return (if scPtrOpt' == Nothing then canDonate else False)

>     reply <- getReply replyPtr
>     assert (replyPrev reply == Nothing) "replyPush: replyPrev must be Nothing"
>     assert (replyNext reply == Nothing && replySc reply == Nothing) "replyPush: both replyNext and replySc must be Nothing"
>     assert (replyCaller reply == Nothing) "replyPush: replyCaller must be Nothing"

>     callerReply <- threadGet tcbReply callerPtr
>     assert (callerReply == Nothing) "replyPush: tcb caller should not be in a existing call stack"

>     setReply replyPtr (reply { replyCaller = Just callerPtr })
>     threadSet (\tcb -> tcb { tcbReply = Just replyPtr }) callerPtr

>     when (scPtrOpt /= Nothing && canDonate) $ do
>         scPtrOpt'' <- threadGet tcbSchedContext calleePtr
>         assert (scPtrOpt'' == Nothing) "replyPush: callee's scheduling context must be Nothing"
>         sc <- getSchedContext (fromJust scPtrOpt)
>         oldCallerPtrOpt <- return $ scReply sc
>         when (oldCallerPtrOpt /= Nothing) $ do
>             oldCallerPtr <- return $ fromJust oldCallerPtrOpt
>             oldCaller <- getReply oldCallerPtr
>             oldCallerNextReply <- getReply $ fromJust $ replyNext oldCaller
>             assert (replySc oldCallerNextReply == scPtrOpt) "replyPush: stack integrity must be satisfied"

>         reply' <- getReply replyPtr
>         setReply replyPtr (reply' { replyPrev = oldCallerPtrOpt, replyNext = Nothing, replySc = scPtrOpt })
>         when (oldCallerPtrOpt /= Nothing) $ do
>             oldCallerPtr <- return $ fromJust oldCallerPtrOpt
>             oldCaller <- getReply oldCallerPtr
>             setReply oldCallerPtr (oldCaller { replyNext = Just replyPtr })
>         setSchedContext (fromJust scPtrOpt) (sc { scReply = Just replyPtr })
>         schedContextDonate (fromJust scPtrOpt) calleePtr

> getReply :: PPtr Reply -> Kernel Reply
> getReply rptr = getObject rptr

> setReply :: PPtr Reply -> Reply -> Kernel ()
> setReply rptr r = setObject rptr r

> getReplyCaller :: PPtr Reply -> Kernel (Maybe (PPtr TCB))
> getReplyCaller r = liftM replyCaller (getReply r)

