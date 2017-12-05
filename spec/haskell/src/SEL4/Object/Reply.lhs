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

> replyRemove :: PPtr Reply -> Kernel ()
> replyRemove replyPtr = do
>     reply <- getReply replyPtr
>     callerOpt <- return $ replyCaller reply
>     assert (callerOpt /= Nothing) "replyRemove: callerOpt must not be Nothing"
>     caller <- return $ fromJust callerOpt
>     scPtrOpt <- return $ replySc reply
>     assert (scPtrOpt /= Nothing) "replyRemove: scPtrOpt must not be Nothing"
>     scPtr <- return $ fromJust scPtrOpt
>     replies <- liftM scReplies $ getSchedContext scPtr
>     replyUnbindCaller caller replyPtr
>     replyUnbindSc scPtr replyPtr
>     when (head replies == replyPtr) $ schedContextDonate scPtr caller

> replyPush :: PPtr TCB -> PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> replyPush caller callee replyPtr canDonate = do
>     scOpt <- threadGet tcbSchedContext caller

>     replyCallerOpt <- getReplyCaller replyPtr
>     when (replyCallerOpt /= Nothing) $ replyRemove replyPtr

>     reply <- getReply replyPtr
>     assert (replyCaller reply == Nothing) "replyPush: reply caller must be Nothing"
>     tcbReplyOpt <- threadGet tcbReply caller
>     assert (tcbReplyOpt == Nothing) "replyPush: the slot containing the reply capability must be Nothing"

>     reply' <- return $ reply { replyCaller = Just caller }
>     setReply replyPtr reply'
>     threadSet (\tcb -> tcb { tcbReply = Just replyPtr }) caller

>     when (scOpt /= Nothing && canDonate) $ do
>         sc <- getSchedContext (fromJust scOpt)
>         setSchedContext (fromJust scOpt) (sc { scReplies = replyPtr : scReplies sc })
>         setReply replyPtr (reply' { replySc = scOpt })
>         schedContextDonate (fromJust scOpt) callee

> getReply :: PPtr Reply -> Kernel Reply
> getReply rptr = getObject rptr

> setReply :: PPtr Reply -> Reply -> Kernel ()
> setReply rptr r = setObject rptr r

> getReplyCaller :: PPtr Reply -> Kernel (Maybe (PPtr TCB))
> getReplyCaller r = liftM replyCaller (getReply r)

