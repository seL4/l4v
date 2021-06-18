%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module specifies the behavior of schedule context objects.

\begin{impdetails}

This module uses the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.SchedContext (
>         schedContextUnbindAllTCBs, invokeSchedContext,
>         invokeSchedControlConfigure, getSchedContext, readSchedContext,
>         schedContextUnbindTCB, schedContextBindTCB, schedContextResume,
>         setSchedContext, updateTimeStamp, commitTime, rollbackTime,
>         refillHd, refillTl, minBudget, minBudgetUs, refillCapacity, refillBudgetCheck,
>         refillBudgetCheckRoundRobin, updateSchedContext, emptyRefill, scBitsFromRefillLength,
>         isCurDomainExpired, refillUnblockCheck,
>         readRefillReady, refillReady, tcbReleaseEnqueue, tcbReleaseDequeue, refillSufficient, postpone,
>         schedContextDonate, maybeDonateSc, maybeReturnSc, schedContextUnbindNtfn,
>         schedContextMaybeUnbindNtfn, isRoundRobin, getRefills, setRefills, refillFull,
>         schedContextCompleteYieldTo, schedContextUnbindYieldFrom,
>         schedContextUnbindReply, schedContextZeroRefillMax, unbindFromSC,
>         schedContextCancelYieldTo, refillAbsoluteMax, schedContextUpdateConsumed,
>         scReleased, setConsumed, refillResetRR, preemptionPoint, refillHdInsufficient,
>         nonOverlappingMergeRefills, headInsufficientLoop
>     ) where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Config
> import SEL4.Machine.Hardware
> import SEL4.Machine.RegisterSet(PPtr(..), Word)
> import SEL4.API.Failures(SyscallError(..))
> import SEL4.API.Types(MessageInfo(..))
> import {-# SOURCE #-} SEL4.Kernel.VSpace(lookupIPCBuffer)
> import SEL4.Model.Failures
> import SEL4.Model.Preemption(KernelP, withoutPreemption)
> import SEL4.Model.PSpace(getObject, readObject, setObject)
> import SEL4.Model.StateData
> import SEL4.Model.Preemption
> import {-# SOURCE #-} SEL4.Object.Notification
> import {-# SOURCE #-} SEL4.Object.Reply
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB(threadGet, threadSet, checkBudget, chargeBudget, replaceAt, updateAt, setTimeArg, setMessageInfo, setMRs)
> import {-# SOURCE #-} SEL4.Kernel.Thread
> import SEL4.API.Invocation(SchedContextInvocation(..), SchedControlInvocation(..))

> import Data.Bits
> import Data.List(delete)
> import Data.Word(Word64)
> import Data.Maybe
> import Control.Monad.State(runState)
> import Control.Monad.Reader(runReaderT)

> import Control.Monad.Except

\end{impdetails}

> minBudget :: Word64
> minBudget = 2 * kernelWCETTicks

> minBudgetUs :: Word64
> minBudgetUs = 2 * kernelWCET_us

> getSchedContext :: PPtr SchedContext -> Kernel SchedContext
> getSchedContext = getObject

> readSchedContext :: PPtr SchedContext -> KernelR SchedContext
> readSchedContext = readObject

> setSchedContext :: PPtr SchedContext -> SchedContext -> Kernel ()
> setSchedContext = setObject

> refillHd :: SchedContext -> Refill
> refillHd sc = scRefills sc !! scRefillHead sc

> updateRefillIndex :: PPtr SchedContext -> (Refill -> Refill) -> Int -> Kernel ()
> updateRefillIndex scPtr f idx = updateSchedContext scPtr (\sc -> sc { scRefills = updateAt idx (scRefills sc) f})

> updateRefillHd :: PPtr SchedContext -> (Refill -> Refill) -> Kernel ()
> updateRefillHd scPtr f = updateSchedContext scPtr (\sc -> sc { scRefills = updateAt (scRefillHead sc) (scRefills sc) f})

> setRefillHd :: PPtr SchedContext -> Refill -> Kernel ()
> setRefillHd scPtr new = updateRefillHd scPtr (\r -> new)

> refillTailIndex :: SchedContext -> Int
> refillTailIndex sc =
>     let index = scRefillHead sc + scRefillCount sc - 1 in
>       if index >= scRefillMax sc
>         then index - scRefillMax sc
>         else index

> scActive :: PPtr SchedContext -> Kernel Bool
> scActive scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefillMax sc > 0

> scReleased :: PPtr SchedContext -> Kernel Bool
> scReleased scPtr = do
>     active <- scActive scPtr
>     ready <- refillReady scPtr
>     return $ active && ready

> refillTl :: SchedContext -> Refill
> refillTl sc = scRefills sc !! refillTailIndex sc

> updateRefillTl :: PPtr SchedContext -> (Refill -> Refill) -> Kernel ()
> updateRefillTl scPtr f = updateSchedContext scPtr (\sc -> sc { scRefills = updateAt (refillTailIndex sc) (scRefills sc) f})

> setRefillTl :: PPtr SchedContext -> Refill -> Kernel ()
> setRefillTl scPtr new = updateRefillTl scPtr (\r -> new)

> setRefills :: PPtr SchedContext -> [Refill] -> Kernel ()
> setRefills scPtr refills = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefills = refills })

> getRefills :: PPtr SchedContext -> Kernel [Refill]
> getRefills scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefills sc

> refillSingle :: PPtr SchedContext -> Kernel Bool
> refillSingle scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefillHead sc == refillTailIndex sc

> refillFull :: PPtr SchedContext -> Kernel Bool
> refillFull scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefillCount sc == scRefillMax sc

> refillEmpty :: PPtr SchedContext -> Kernel Bool
> refillEmpty scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefillCount sc == 0

> updateSchedContext :: PPtr SchedContext -> (SchedContext -> SchedContext) -> Kernel ()
> updateSchedContext scPtr f = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (f sc)

> readRefillNext :: PPtr SchedContext -> Int -> KernelR Int
> readRefillNext scPtr index = do
>     sc <- readSchedContext scPtr
>     return $ if (index == scRefillMax sc - 1) then 0 else index + 1

> getRefillNext :: PPtr SchedContext -> Int -> Kernel Int
> getRefillNext scPtr index = getsJust (readRefillNext scPtr index)

> updateRefillNext :: PPtr SchedContext -> (Refill -> Refill) -> Int -> Kernel ()
> updateRefillNext scPtr f index = do
>     updateSchedContext scPtr (\sc -> sc { scRefills = updateAt (refillNextIndex index sc) (scRefills sc) f})

> refillIndex :: Int -> SchedContext -> Refill
> refillIndex index sc = scRefills sc !! index

> refillNextIndex :: Int -> SchedContext -> Int
> refillNextIndex index sc = if (index == scRefillMax sc - 1) then 0 else index + 1

> -- Odd argument order plays well with `updateSchedContext`.
> setRefillIndex :: Int -> Refill -> SchedContext -> SchedContext
> setRefillIndex index refill sc =
>     sc { scRefills = replaceAt index (scRefills sc) refill }

> readRefillSize :: PPtr SchedContext -> KernelR Int
> readRefillSize scPtr = liftM scRefillCount $ readSchedContext scPtr

> getRefillSize :: PPtr SchedContext -> Kernel Int
> getRefillSize scPtr = getsJust (readRefillSize scPtr)

> refillsCapacity :: Ticks -> [Refill] -> Int -> Ticks
> refillsCapacity usage refills headIndex =
>     if rAmount (refills !! headIndex) < usage
>         then 0
>         else rAmount (refills !! headIndex) - usage

> refillCapacity :: PPtr SchedContext -> Ticks -> Kernel Ticks
> refillCapacity scPtr usage = do
>     refills <- getRefills scPtr
>     sc <- getSchedContext scPtr
>     return $ refillsCapacity usage refills (scRefillHead sc)

> sufficientRefills :: Ticks -> [Refill] -> Int -> Bool
> sufficientRefills usage refills headIndex = minBudget <= refillsCapacity usage refills headIndex

> refillSufficient :: PPtr SchedContext -> Ticks -> Kernel Bool
> refillSufficient scPtr usage = do
>     refills <- getRefills scPtr
>     sc <- getSchedContext scPtr
>     return $ sufficientRefills usage refills (scRefillHead sc)

> refillPopHead :: PPtr SchedContext -> Kernel Refill
> refillPopHead scPtr = do
>     refill <- liftM refillHd $ getSchedContext scPtr
>     updateSchedContext scPtr $ \sc -> sc { scRefillHead = refillNextIndex (scRefillHead sc) sc,
>                                     scRefillCount = scRefillCount sc - 1 }
>     return refill

> refillAddTail :: PPtr SchedContext -> Refill -> Kernel ()
> refillAddTail scPtr refill = do
>     sc <- getSchedContext scPtr
>     assert (scRefillCount sc < scRefillMax sc) "cannot add beyond queue size"
>     newTail <- return $ refillNextIndex (refillTailIndex sc) sc
>     updateSchedContext scPtr (\sc -> sc { scRefills = replaceAt (refillNextIndex (refillTailIndex sc) sc) (scRefills sc) refill, scRefillCount = scRefillCount sc + 1})

> maybeAddEmptyTail :: PPtr SchedContext -> Kernel ()
> maybeAddEmptyTail scPtr = do
>     roundRobin <- isRoundRobin scPtr
>     when roundRobin $ do
>         sc <- getSchedContext scPtr
>         tail <- return $ (Refill { rTime = rTime (refillHd sc), rAmount = 0 })
>         refillAddTail scPtr tail

> refillNew :: PPtr SchedContext -> Int -> Ticks -> Ticks -> Kernel ()
> refillNew scPtr maxRefills budget period = do
>     curTime <- getCurTime
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scPeriod = period })
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scBudget = budget })
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefillHead = 0 })
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefillCount = 1 })
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefillMax = maxRefills })
>     setRefillHd scPtr (Refill { rTime = curTime, rAmount = budget })
>     maybeAddEmptyTail scPtr

> readRefillReady :: PPtr SchedContext -> KernelR Bool
> readRefillReady scPtr = do
>     sc <- readSchedContext scPtr
>     curTime <- readCurTime
>     return $ rTime (refillHd sc) <= curTime + kernelWCETTicks

> refillReady :: PPtr SchedContext -> Kernel Bool
> refillReady scPtr = getsJust (readRefillReady scPtr)

> refillUpdate :: PPtr SchedContext -> Ticks -> Ticks -> Int -> Kernel ()
> refillUpdate scPtr newPeriod newBudget newMaxRefills = do
>     sc <- getSchedContext scPtr
>     let head = refillHd sc
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefillHead = 0 })
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefillCount = 1 })
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefillMax = newMaxRefills })
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr $ setRefillIndex 0 head sc
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scPeriod = newPeriod })
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scBudget = newBudget })
>     whenM (refillReady scPtr) $ do
>         curTime <- getCurTime
>         updateRefillHd scPtr $ \r -> r { rTime = curTime }
>     head <- liftM refillHd $ getSchedContext scPtr
>     if (rAmount head >= newBudget)
>       then do
>         updateRefillHd scPtr $ \r -> r { rAmount = newBudget }
>         maybeAddEmptyTail scPtr
>       else do
>         let unused = newBudget - rAmount head
>         let new = Refill { rTime = rTime head + newPeriod, rAmount = unused }
>         refillAddTail scPtr new

> scheduleUsed :: PPtr SchedContext -> Refill -> Kernel ()
> scheduleUsed scPtr new = do
>     sc <- getSchedContext scPtr
>     assert (scRefillMax sc > 0) "scPtr should be active"
>     empty <- refillEmpty scPtr
>     if empty
>         then refillAddTail scPtr new
>         else do
>          full <- refillFull scPtr
>          if (rTime (refillTl sc) + rAmount (refillTl sc) >= rTime new)
>               then do
>                 let tl = refillTl sc
>                 let tl' = tl { rAmount = rAmount tl + rAmount new}
>                 setRefillTl scPtr tl'
>               else if (not full)
>                         then refillAddTail scPtr new
>                         else do
>                           let tl = refillTl sc
>                           let tl' = tl { rTime = rTime new - rAmount tl,
>                                          rAmount = rAmount tl + rAmount new }
>                           setRefillTl scPtr tl'

> refillResetRR :: PPtr SchedContext -> Kernel ()
> refillResetRR scPtr = do
>     updateSchedContext scPtr (\sc -> sc { scRefills = updateAt (scRefillHead sc) (scRefills sc) (\hd -> hd { rAmount = rAmount hd + rAmount (refillTl sc)})})
>     updateRefillTl scPtr (\last -> last { rAmount = 0})

> refillHdInsufficient :: PPtr SchedContext -> KernelR Bool
> refillHdInsufficient scPtr = do
>     sc <- readSchedContext scPtr
>     return $ rAmount (refillHd sc) < minBudget

> nonOverlappingMergeRefills :: PPtr SchedContext -> Kernel ()
> nonOverlappingMergeRefills scPtr = do
>     sc <- getSchedContext scPtr
>     assert (1 < scRefillCount sc) "if head is insufficient, there must be at least 2 refills"
>     old_head <- refillPopHead scPtr
>     updateRefillHd scPtr $ \head -> head { rAmount = rAmount head + rAmount old_head }
>     updateRefillHd scPtr $ \head -> head { rTime = rTime head - rAmount old_head}

> headInsufficientLoop :: PPtr SchedContext -> Kernel ()
> headInsufficientLoop scPtr = whileLoop (const (fromJust . runReaderT (refillHdInsufficient scPtr))) (const (nonOverlappingMergeRefills scPtr)) ()

> mergeRefills :: PPtr SchedContext -> Kernel ()
> mergeRefills scPtr = do
>     old_head <- refillPopHead scPtr
>     updateRefillHd scPtr $ \head -> head { rTime = rTime old_head,
>                                            rAmount = rAmount head + rAmount old_head }

> refillHeadOverlapping :: PPtr SchedContext -> KernelR Bool
> refillHeadOverlapping scPtr = do
>     head <- liftM refillHd $ readSchedContext scPtr
>     let amount = rAmount head
>     let tail = rTime head + amount
>     headIndex <- liftM scRefillHead $ readSchedContext scPtr
>     nextRefillIndex <- readRefillNext scPtr headIndex
>     nextRefill <- liftM (refillIndex nextRefillIndex) $ readSchedContext scPtr
>     let enough_time = rTime nextRefill <= tail
>     refills <- readRefillSize scPtr
>     return (refills > 1 && enough_time)

> refillHeadOverlappingLoop :: PPtr SchedContext -> Kernel ()
> refillHeadOverlappingLoop scPtr =
>        whileLoop (const (fromJust . runReaderT (refillHeadOverlapping scPtr))) (const (mergeRefills scPtr)) ()

> headTimeBuffer :: Ticks -> KernelR Bool
> headTimeBuffer usage = do
>     scPtr <- readCurSc
>     sc <- readSchedContext scPtr
>     return $ rAmount (refillHd sc) <= usage && (maxBound :: Word64) - rTime (refillHd sc) >= 5 * usToTicks maxPeriodUs

> handleOverrunLoopBody :: Ticks -> Kernel Ticks
> handleOverrunLoopBody usage = do
>     scPtr <- getCurSc
>     single <- refillSingle scPtr
>     sc <- getSchedContext scPtr

>     usage' <- return (usage - rAmount (refillHd sc))

>     if single
>        then updateRefillHd scPtr $ \r -> r { rTime = rTime r + scPeriod sc}
>        else do
>          old_head <- refillPopHead scPtr
>          let new = old_head { rTime = rTime old_head + scPeriod sc}
>          scheduleUsed scPtr new

>     return usage'

> handleOverrunLoop :: Ticks -> Kernel Ticks
> handleOverrunLoop usage =
>     whileLoop (\usage -> fromJust . runReaderT (headTimeBuffer usage)) (\usage -> handleOverrunLoopBody usage) usage

> refillBudgetCheck :: Ticks -> Kernel ()
> refillBudgetCheck usage = do
>     scPtr <- getCurSc

>     active <- scActive scPtr
>     assert active "CurSc should be active"

>     roundRobin <- isRoundRobin scPtr
>     assert (not roundRobin) "the current sc should not be round robin when this function is called"

>     usage' <- handleOverrunLoop usage

>     sc <- getSchedContext scPtr
>     newHeadAmount <- return (rAmount (refillHd sc))

>     when (usage' > 0 && usage' < newHeadAmount) $ do
>       used <- return Refill { rTime = rTime (refillHd sc) + (scPeriod sc),
>                               rAmount = usage'}
>       setRefillHd scPtr (Refill { rTime = rTime (refillHd sc) + usage',
>                                   rAmount = rAmount (refillHd sc) - usage' })
>       scheduleUsed scPtr used

      Ensure that the rAmount of the head refill is at least minBudget

>     headInsufficientLoop scPtr

> refillBudgetCheckRoundRobin :: Ticks -> Kernel ()
> refillBudgetCheckRoundRobin usage = do
>     scPtr <- getCurSc
>     updateRefillHd scPtr $ \r -> r { rAmount = rAmount r - usage }
>     updateRefillTl scPtr $ \r -> r { rAmount = rAmount r + usage }

> refillUnblockCheck :: PPtr SchedContext -> Kernel ()
> refillUnblockCheck scPtr = do
>       scactive <- scActive scPtr
>       assert scactive "scPtr should be active"
>       roundRobin <- isRoundRobin scPtr
>       ready <- refillReady scPtr
>       when ((not roundRobin) && ready) $ do
>         setReprogramTimer True
>         curTime <- getCurTime
>         updateRefillHd scPtr $ \head -> head { rTime = curTime + kernelWCETTicks }
>         refillHeadOverlappingLoop scPtr

> schedContextUpdateConsumed :: PPtr SchedContext -> Kernel Time
> schedContextUpdateConsumed scPtr = do
>     sc <- getSchedContext scPtr
>     consumed <- return $ scConsumed sc
>     if consumed >= maxTicksToUs
>         then do
>             setSchedContext scPtr $ sc { scConsumed = scConsumed sc - maxTicksToUs }
>             return $ ticksToUs maxTicksToUs
>         else do
>             setSchedContext scPtr $ sc { scConsumed = 0 }
>             return $ ticksToUs consumed

> setConsumed :: PPtr SchedContext -> Maybe (PPtr Word) -> Kernel ()
> setConsumed scPtr buffer = do
>     consumed <- schedContextUpdateConsumed scPtr
>     tptr <- getCurThread
>     sent <- setMRs tptr buffer (setTimeArg consumed)
>     setMessageInfo tptr $ MI sent 0 0 0

> schedContextBindTCB :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextBindTCB scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr
>     setSchedContext scPtr $ sc { scTCB = Just tcbPtr }
>     schedContextResume scPtr
>     schedulable <- isSchedulable tcbPtr
>     when schedulable $ do
>         tcbSchedEnqueue tcbPtr
>         rescheduleRequired

> schedContextBindNtfn :: PPtr SchedContext -> PPtr Notification -> Kernel ()
> schedContextBindNtfn sc ntfn = do
>     n <- getNotification ntfn
>     setNotification ntfn (n { ntfnSc = Just sc })
>     s <- getSchedContext sc
>     setSchedContext sc (s { scNtfn = Just ntfn })

> schedContextUnbindTCB :: PPtr SchedContext -> Kernel ()
> schedContextUnbindTCB scPtr = do
>     stateAssert sym_refs_asrt "Assert that `sym_refs (state_refs_of' s)` holds"
>     sc <- getSchedContext scPtr
>     let tptrOpt = scTCB sc
>     assert (tptrOpt /= Nothing) "schedContextUnbind: option of TCB pointer must not be Nothing"
>     let tptr = fromJust tptrOpt
>     cur <- getCurThread
>     when (tptr == cur) $ rescheduleRequired
>     tcbSchedDequeue tptr
>     tcbReleaseRemove tptr
>     threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tptr
>     setSchedContext scPtr $ sc { scTCB = Nothing }

> schedContextUnbindNtfn :: PPtr SchedContext -> Kernel ()
> schedContextUnbindNtfn scPtr = do
>     stateAssert sym_refs_asrt
>             "Assert that `sym_refs (state_refs_of' s)` holds"
>     sc <- getSchedContext scPtr
>     case scNtfn sc of
>         Nothing -> return ()
>         Just ntfnPtr -> do
>             ntfn <- getNotification ntfnPtr
>             setNotification ntfnPtr (ntfn { ntfnSc = Nothing })
>             setSchedContext scPtr (sc { scNtfn = Nothing })

> schedContextMaybeUnbindNtfn :: PPtr Notification -> Kernel ()
> schedContextMaybeUnbindNtfn ntfnPtr = do
>     scOpt <- liftM ntfnSc $ getNotification ntfnPtr
>     case scOpt of
>         Nothing -> return ()
>         Just scPtr -> schedContextUnbindNtfn scPtr

> schedContextUnbindAllTCBs :: PPtr SchedContext -> Kernel ()
> schedContextUnbindAllTCBs scPtr = do
>     sc <- getSchedContext scPtr
>     when (scTCB sc /= Nothing) $ schedContextUnbindTCB scPtr

> schedContextCancelYieldTo :: PPtr TCB -> Kernel ()
> schedContextCancelYieldTo tptr = do
>     scPtrOpt <- threadGet tcbYieldTo tptr
>     when (scPtrOpt /= Nothing) $ do
>         scPtr <- return $ fromJust scPtrOpt
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scYieldFrom = Nothing })
>         threadSet (\tcb -> tcb { tcbYieldTo = Nothing }) tptr

> schedContextCompleteYieldTo :: PPtr TCB -> Kernel ()
> schedContextCompleteYieldTo tptr = do
>     scPtrOpt <- threadGet tcbYieldTo tptr
>     when (scPtrOpt /= Nothing) $ do
>         scPtr <- return $ fromJust scPtrOpt
>         bufferOpt <- lookupIPCBuffer True tptr
>         setConsumed scPtr bufferOpt
>         schedContextCancelYieldTo tptr

> schedContextUnbindYieldFrom :: PPtr SchedContext -> Kernel ()
> schedContextUnbindYieldFrom scPtr = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     sc <- getSchedContext scPtr
>     when (scYieldFrom sc /= Nothing) $
>         schedContextCompleteYieldTo $ fromJust $ scYieldFrom sc

> schedContextUnbindReply :: PPtr SchedContext -> Kernel ()
> schedContextUnbindReply scPtr = do
>     stateAssert sym_refs_asrt "Assert that `sym_refs (state_refs_of' s)` holds"
>     sc <- getSchedContext scPtr
>     replyPtrOpt <- return $ scReply sc
>     when (replyPtrOpt /= Nothing) $ do
>         replyPtr <- return $ fromJust replyPtrOpt
>         updateReply replyPtr (\reply -> reply { replyNext = Nothing })
>         setSchedContext scPtr (sc { scReply = Nothing })

> schedContextZeroRefillMax :: PPtr SchedContext -> Kernel ()
> schedContextZeroRefillMax scPtr = do
>     updateSchedContext scPtr $ (\sc -> sc { scRefillMax = 0 })

> unbindFromSC :: PPtr TCB -> Kernel ()
> unbindFromSC tptr = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     sc_ptr_opt <- threadGet tcbSchedContext tptr
>     when (sc_ptr_opt /= Nothing) $ do
>         let scPtr = fromJust sc_ptr_opt
>         schedContextUnbindTCB scPtr
>         sc <- getSchedContext scPtr
>         when (scYieldFrom sc /= Nothing) $
>             schedContextCompleteYieldTo $ fromJust $ scYieldFrom sc

> postpone :: PPtr SchedContext -> Kernel ()
> postpone scPtr = do
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTCB sc
>     tcbSchedDequeue tptr
>     tcbReleaseEnqueue tptr
>     setReprogramTimer True

> schedContextResume :: PPtr SchedContext -> Kernel ()
> schedContextResume scPtr = do
>     sc <- getSchedContext scPtr
>     tptrOpt <- return $ scTCB sc
>     assert (tptrOpt /= Nothing) "schedContextResume: option of TCB pointer must not be Nothing"
>     tptr <- return $ fromJust tptrOpt
>     schedulable <- isSchedulable tptr
>     when schedulable $ do
>         ready <- refillReady scPtr
>         sufficient <- refillSufficient scPtr 0
>         when (not (ready && sufficient)) $ postpone scPtr

> contextYieldToUpdateQueues :: PPtr SchedContext -> Kernel Bool
> contextYieldToUpdateQueues scPtr = do
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTCB sc
>     schedulable <- isSchedulable tptr
>     if schedulable
>         then do
>             refillUnblockCheck scPtr
>             ctPtr <- getCurThread
>             curprio <- threadGet tcbPriority ctPtr
>             prio <- threadGet tcbPriority tptr
>             if prio < curprio
>                 then do
>                     tcbSchedDequeue tptr
>                     tcbSchedEnqueue tptr
>                     return True
>                 else do
>                     threadSet (\tcb -> tcb { tcbYieldTo = Just scPtr }) ctPtr
>                     setSchedContext scPtr (sc { scYieldFrom = Just ctPtr })
>                     tcbSchedDequeue tptr
>                     tcbSchedEnqueue ctPtr
>                     tcbSchedEnqueue tptr
>                     rescheduleRequired
>                     return False
>         else return True

> schedContextYieldTo :: PPtr SchedContext -> Maybe (PPtr Word) -> Kernel ()
> schedContextYieldTo scPtr buffer = do
>     sc <- getSchedContext scPtr
>     scYieldFromOpt <- return $ scYieldFrom sc
>     when (scYieldFromOpt /= Nothing) $
>         schedContextCompleteYieldTo $ fromJust scYieldFromOpt
>     schedContextResume scPtr
>     return_now <- contextYieldToUpdateQueues scPtr
>     when return_now $ setConsumed scPtr buffer

> invokeSchedContext :: SchedContextInvocation -> Kernel ()
> invokeSchedContext iv = case iv of
>     InvokeSchedContextConsumed scPtr buffer -> setConsumed scPtr buffer
>     InvokeSchedContextBind scPtr cap -> case cap of
>         ThreadCap tcbPtr -> schedContextBindTCB scPtr tcbPtr
>         NotificationCap ntfnPtr _ _ _ -> schedContextBindNtfn scPtr ntfnPtr
>         _ -> return ()
>     InvokeSchedContextUnbindObject scPtr cap -> case cap of
>         ThreadCap _ -> schedContextUnbindTCB scPtr
>         NotificationCap _ _ _ _ -> schedContextUnbindNtfn scPtr
>         _ -> return ()
>     InvokeSchedContextUnbind scPtr -> do
>         schedContextUnbindAllTCBs scPtr
>         schedContextUnbindNtfn scPtr
>         sc <- getSchedContext scPtr
>         let replyPtrOpt = scReply sc
>         when (replyPtrOpt /= Nothing) $ do
>             let replyPtr = fromJust replyPtrOpt
>             updateReply replyPtr (\reply -> reply { replyNext = Nothing })
>             setSchedContext scPtr $ sc { scReply = Nothing }
>     InvokeSchedContextYieldTo scPtr buffer -> do
>         schedContextYieldTo scPtr buffer

> getTCBSc :: PPtr TCB -> Kernel SchedContext
> getTCBSc tcbPtr = do
>     scOpt <- threadGet tcbSchedContext tcbPtr
>     assert (scOpt /= Nothing) "getTCBSc: SchedContext pointer must not be Nothing"
>     getSchedContext $ fromJust scOpt

> getScTime :: PPtr TCB -> Kernel Time
> getScTime tcbPtr = do
>     sc <- getTCBSc tcbPtr
>     return $ rTime (refillHd sc)

> schedContextDonate :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextDonate scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     fromOpt <- return $ scTCB sc
>     when (fromOpt /= Nothing) $ do
>         from <- return $ fromJust fromOpt
>         tcbSchedDequeue from
>         tcbReleaseRemove from
>         threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) from
>         cur <- getCurThread
>         action <- getSchedulerAction
>         case action of
>             SwitchToThread candidate -> when (candidate == from || from == cur) rescheduleRequired
>             _ -> when (from == cur) rescheduleRequired
>     setSchedContext scPtr (sc { scTCB = Just tcbPtr })
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr

> invokeSchedControlConfigure :: SchedControlInvocation -> Kernel ()
> invokeSchedControlConfigure iv = case iv of
>     InvokeSchedControlConfigure scPtr budget period mRefills badge -> do
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr $ sc { scBadge = badge }
>         when (scTCB sc /= Nothing) $ do
>             tcbReleaseRemove $ fromJust $ scTCB sc
>             tcbSchedDequeue $ fromJust $ scTCB sc
>             curSc <- getCurSc
>             when (curSc == scPtr) $ do
>                 budgetEnough <- checkBudget
>                 when budgetEnough $ commitTime

>         runnable <- isRunnable $ fromJust $ scTCB sc
>         if period == budget
>             then refillNew scPtr minRefills budget 0
>             else do
>               sc <- getSchedContext scPtr
>               if scRefillMax sc > 0 && scTCB sc /= Nothing && runnable
>                   then refillUpdate scPtr period budget mRefills
>                   else refillNew scPtr mRefills budget period

>         sc <- getSchedContext scPtr
>         when (scTCB sc /= Nothing && scRefillMax sc > 0) $ do
>             schedContextResume scPtr
>             ctPtr <- getCurThread
>             if (fromJust $ scTCB sc) == ctPtr
>                 then rescheduleRequired
>                 else when runnable $ possibleSwitchTo $ fromJust $ scTCB sc

> isRoundRobin :: PPtr SchedContext -> Kernel Bool
> isRoundRobin scPtr = do
>     sc <- getSchedContext scPtr
>     return (scPeriod sc == 0)

> isCurDomainExpired :: Kernel Bool
> isCurDomainExpired = do
>     domainTime <- getDomainTime
>     consumedTime <- getConsumedTime
>     return $! domainTime < consumedTime + minBudget

> commitTime :: Kernel ()
> commitTime = do
>     scPtr <- getCurSc
>     refillMax <- liftM scRefillMax $ getSchedContext scPtr
>     when (refillMax > 0) $ do
>       consumed <- getConsumedTime
>       when (consumed > 0) $ do
>         ifM (isRoundRobin scPtr)
>           (refillBudgetCheckRoundRobin consumed)
>           (refillBudgetCheck consumed)
>       updateSchedContext scPtr $ \sc -> sc { scConsumed = scConsumed sc + consumed }
>     when (numDomains > 1) $ do
>       consumed <- getConsumedTime
>       domainTime <- getDomainTime
>       time' <- return $ if (domainTime < consumed) then 0 else (domainTime - consumed)
>       setDomainTime time'
>     setConsumedTime 0

> rollbackTime :: Kernel ()
> rollbackTime = do
>     reprogram <- getReprogramTimer
>     consumed <- getConsumedTime
>     assert (not reprogram || consumed == 0) "rollbackTime: it is invalid to rollback time if we have already acted on the new time"
>     curTime <- getCurTime
>     setCurTime (curTime - consumed)
>     setConsumedTime 0

> updateTimeStamp :: Kernel ()
> updateTimeStamp = do
>     prevTime <- getCurTime
>     curTime' <- doMachineOp getCurrentTime
>     setCurTime curTime'
>     consumed <- getConsumedTime
>     setConsumedTime (consumed + curTime' - prevTime)

> maybeDonateSc :: PPtr TCB -> PPtr Notification -> Kernel ()
> maybeDonateSc tcbPtr ntfnPtr = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     scOpt <- threadGet tcbSchedContext tcbPtr
>     when (scOpt == Nothing) $ do
>         scPtrOpt <- liftM ntfnSc (getNotification ntfnPtr)
>         case scPtrOpt of
>             Nothing -> return ()
>             Just scPtr -> do
>                 scTCB <- liftM scTCB $ getSchedContext scPtr
>                 when (scTCB == Nothing) $ do
>                     schedContextDonate scPtr tcbPtr
>                     curSc <- getCurSc
>                     when (scPtr /= curSc) $ refillUnblockCheck scPtr
>                     schedContextResume scPtr

> maybeReturnSc :: PPtr Notification -> PPtr TCB -> Kernel ()
> maybeReturnSc ntfnPtr tcbPtr = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     nscOpt <- liftM ntfnSc $ getNotification ntfnPtr
>     tscOpt <- threadGet tcbSchedContext tcbPtr
>     when (nscOpt == tscOpt && nscOpt /= Nothing) $ do
>         threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tcbPtr
>         scPtr <- return $ fromJust nscOpt
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scTCB = Nothing })
>         cur <- getCurThread
>         when (tcbPtr == cur) rescheduleRequired

> tcbReleaseEnqueue :: PPtr TCB -> Kernel ()
> tcbReleaseEnqueue tcbPtr = do
>     time <- getScTime tcbPtr
>     qs <- getReleaseQueue
>     times <- mapM getScTime qs
>     qst <- return $ zip qs times
>     qst' <- return $ filter (\(_,t') -> t' <= time) qst ++ [(tcbPtr, time)] ++ filter (\(_,t') -> not (t' <= time)) qst
>     when (filter (\(_,t') -> t' <= time) qst == []) $
>         setReprogramTimer True
>     setReleaseQueue (map fst qst')
>     threadSet (\t -> t { tcbInReleaseQueue = True }) tcbPtr

> tcbReleaseDequeue :: Kernel (PPtr TCB)
> tcbReleaseDequeue = do
>     qs <- getReleaseQueue
>     tcbPtr <- return $ head qs
>     setReleaseQueue $ tail qs
>     threadSet (\t -> t { tcbInReleaseQueue = False }) tcbPtr
>     setReprogramTimer True
>     return tcbPtr

In preemptible code, the kernel may explicitly mark a preemption point with the "preemptionPoint" function. The preemption will only be taken if an interrupt has occurred and the preemption point has been called "workUnitsLimit" times.

> workUnitsLimit = 0x64

> preemptionPoint :: KernelP ()
> preemptionPoint = do
>     withoutPreemption $ modifyWorkUnits (\op -> op + 1)
>     workUnits <- withoutPreemption $ getWorkUnits
>     when (workUnitsLimit <= workUnits) $ do
>       withoutPreemption $ setWorkUnits 0
>       preempt <- withoutPreemption $ doMachineOp (getActiveIRQ True)
>       if isJust preempt
>           then throwError ()
>           else do
>              withoutPreemption $ updateTimeStamp
>              csc <- withoutPreemption $ getCurSc
>              consumed <- withoutPreemption $ getConsumedTime
>              test <- withoutPreemption $ andM (scActive csc) (refillSufficient csc consumed)
>              domExp <- withoutPreemption $ isCurDomainExpired
>              if (not test || domExp)
>                   then throwError ()
>                   else return ()
