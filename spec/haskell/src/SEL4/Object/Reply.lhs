%
% Copyright 2018, Data61, CSIRO
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(DATA61_GPL)
%

This module specifies the behavior of reply objects.

> module SEL4.Object.Reply (
>         replyClear, replyRemove, replyPush, replyUnlinkTCB, getReply, setReply, getReplyTCB,
>         replyRemoveTCB, setReplyTCB, getReplySc, setReplySc, replyUnlinkSc
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.Machine SEL4.Model SEL4.Object.Structures #-}
% {-# BOOT-EXPORTS: replyClear replyRemove replyRemoveTCB replyPush replyUnlinkTCB getReply setReply getReplyTCB getReplySc setReplySc replyUnlinkSc #-}

> import {-# SOURCE #-} SEL4.Kernel.Thread(getThreadState, setThreadState)
> import SEL4.Machine.RegisterSet(PPtr)
> import SEL4.Model.StateData
> import SEL4.Model.PSpace(getObject, setObject)
> import SEL4.Object.SchedContext
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB

> import Data.List
> import Data.Maybe(fromJust)

\end{impdetails}

> replyRemove :: PPtr Reply -> Kernel ()
> replyRemove replyPtr = do
>     reply <- getReply replyPtr
>     assert (replyTCB reply /= Nothing) "caller thread must not be Nothing"
>     let caller = fromJust $ replyTCB reply
>     assert (replySc reply /= Nothing)
>         "reply's associating scheduling context must not be Nothing"
>     let scPtr = fromJust $ replySc reply
>     sc <- getSchedContext scPtr
>     callerSc <- threadGet tcbSchedContext caller
>     replyUnlinkTCB replyPtr
>     replyUnlinkSc scPtr replyPtr
>     when ((head $ scReplies sc) == replyPtr && callerSc == Nothing) $
>         schedContextDonate scPtr caller

> replyPush :: PPtr TCB -> PPtr TCB -> PPtr Reply -> Bool -> Kernel ()
> replyPush caller callee replyPtr canDonate = do
>     scCaller <- threadGet tcbSchedContext caller
>     replyTCBOpt <- getReplyTCB replyPtr
>     assert (replyTCBOpt == Nothing) "replyPtr must have no associated TCB"
>     scCallee <- threadGet tcbSchedContext callee
>     let canDonate = if (scCallee == Nothing) then canDonate else False
>     stateCaller <- getThreadState caller
>     case stateCaller of
>         BlockedOnReceive _ (Just r) -> fail "caller must have no reply"
>         BlockedOnReply (Just r) -> fail "caller must have no reply"
>         _ -> return ()
>     stateCallee <- getThreadState callee
>     case stateCallee of
>         BlockedOnReceive e _ -> setThreadState (BlockedOnReceive e Nothing) callee
>         BlockedOnReply _ -> setThreadState (BlockedOnReply Nothing) callee
>         _ -> return ()
>     setReplyTCB (Just caller) replyPtr
>     setThreadState (BlockedOnReply (Just replyPtr)) caller
>     when (scCaller /= Nothing && canDonate) $ do
>         scCallee <- threadGet tcbSchedContext callee
>         assert (scCallee == Nothing) "callee must have no scheduling context"
>         scKoCaller <- getSchedContext $ fromJust scCaller
>         setSchedContext (fromJust scCaller)
>             (scKoCaller { scReplies = [replyPtr] ++ scReplies scKoCaller })
>         setReplySc scCaller replyPtr
>         schedContextDonate (fromJust scCaller) callee

> replyUnlinkTCB :: PPtr Reply -> Kernel ()
> replyUnlinkTCB rptr = do
>     tptrOpt <- getReplyTCB rptr
>     setReplyTCB Nothing rptr
>     setThreadState Inactive $ fromJust tptrOpt

> replyUnlinkSc :: PPtr SchedContext -> PPtr Reply -> Kernel ()
> replyUnlinkSc scPtr rptr = do
>     sc <- getSchedContext scPtr
>     r <- getReply rptr
>     setReplySc Nothing rptr
>     setSchedContext scPtr (sc { scReplies = delete rptr (scReplies sc) })

> replyRemoveTCB :: PPtr TCB -> Kernel ()
> replyRemoveTCB tptr = do
>     state <- getThreadState tptr
>     assert (isReply state) "replyRemoveTCB: thread state must be BlockedOnReply"
>     rptr <- return $ fromJust $ replyObject state
>     replyRemove rptr

> getReply :: PPtr Reply -> Kernel Reply
> getReply rptr = getObject rptr

> setReply :: PPtr Reply -> Reply -> Kernel ()
> setReply rptr r = setObject rptr r

> getReplyTCB :: PPtr Reply -> Kernel (Maybe (PPtr TCB))
> getReplyTCB r = liftM replyTCB (getReply r)

> setReplyTCB :: Maybe (PPtr TCB) -> PPtr Reply -> Kernel ()
> setReplyTCB tptrOpt rptr = do
>     r <- getReply rptr
>     setReply rptr r { replyTCB = tptrOpt }

> getReplySc :: PPtr Reply -> Kernel (Maybe (PPtr SchedContext))
> getReplySc r = liftM replySc (getReply r)

> setReplySc :: Maybe (PPtr SchedContext) -> PPtr Reply -> Kernel ()
> setReplySc scptrOpt rptr = do
>     r <- getReply rptr
>     setReply rptr r { replySc = scptrOpt }

> replyClear :: PPtr Reply -> Kernel ()
> replyClear rptr = do
>     tptrOpt <- getReplyTCB rptr
>     assert (tptrOpt /= Nothing) "replyClear: TCB pointer should not be nothing."
>     state <- getThreadState $ fromJust tptrOpt
>     case state of
>         BlockedOnReply _ -> replyRemove rptr
>         BlockedOnReceive {} -> replyUnlinkTCB rptr
>         _ -> fail "replyClear: invalid state of replyTCB"

