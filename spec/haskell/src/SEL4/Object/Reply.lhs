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
>     scPtrOptDonated <- threadGet tcbSchedContext callerPtr
>     replyCallerPtrOpt <- getReplyCaller replyPtr
>     when (replyCallerPtrOpt /= Nothing) $ replyRemove replyPtr

>     scPtrOptCallee <- threadGet tcbSchedContext calleePtr
>     canDonate <- return (if scPtrOptCallee /= Nothing then False else canDonate)

>     reply <- getReply replyPtr
>     assert (replyPrev reply == Nothing) "replyPush: replyPrev must be Nothing"
>     assert (replyNext reply == Nothing && replySc reply == Nothing) "replyPush: both replyNext and replySc must be Nothing"
>     assert (replyCaller reply == Nothing) "replyPush: replyCaller must be Nothing"

>     callerReply <- threadGet tcbReply callerPtr
>     assert (callerReply == Nothing) "replyPush: tcb caller must not have a reply associated"

>     setReply replyPtr (reply { replyCaller = Just callerPtr })
>     threadSet (\tcb -> tcb { tcbReply = Just replyPtr }) callerPtr

>     when (scPtrOptDonated /= Nothing && canDonate) $ do
>         assert (scPtrOptCallee == Nothing) "replyPush: callee must not have a scheduling context"
>         scDonated <- getSchedContext (fromJust scPtrOptDonated)
>         oldReplyPtrOpt <- return $ scReply scDonated
>         when (oldReplyPtrOpt /= Nothing) $ do
>             oldReplyPtr <- return $ fromJust oldReplyPtrOpt
>             oldReply <- getReply oldReplyPtr
>             assert (replySc oldReply == scPtrOptDonated) "replyPush: scheduling context and reply must have reference to each other"

>         reply' <- getReply replyPtr
>         setReply replyPtr (reply' { replyPrev = oldReplyPtrOpt, replyNext = Nothing, replySc = scPtrOptDonated })
>         when (oldReplyPtrOpt /= Nothing) $ do
>             oldReplyPtr <- return $ fromJust oldReplyPtrOpt
>             oldReply <- getReply oldReplyPtr
>             setReply oldReplyPtr (oldReply { replyNext = Just replyPtr, replySc = Nothing })
>         setSchedContext (fromJust scPtrOptDonated) (scDonated { scReply = Just replyPtr })
>         schedContextDonate (fromJust scPtrOptDonated) calleePtr

> getReply :: PPtr Reply -> Kernel Reply
> getReply rptr = getObject rptr

> setReply :: PPtr Reply -> Reply -> Kernel ()
> setReply rptr r = setObject rptr r

> getReplyCaller :: PPtr Reply -> Kernel (Maybe (PPtr TCB))
> getReplyCaller r = liftM replyCaller (getReply r)

