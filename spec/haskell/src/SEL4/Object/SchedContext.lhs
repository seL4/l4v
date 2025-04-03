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
>         invokeSchedControlConfigureFlags, getSchedContext, readSchedContext,
>         schedContextUnbindTCB, schedContextBindTCB, schedContextResume,
>         setSchedContext, updateTimeStamp, commitTime, rollbackTime,
>         refillHd, refillTl, minBudget, minBudgetUs,
>         readRefillIndex, readRefillHead, getRefillHead,
>         refillCapacity, readRefillCapacity, getRefillCapacity, refillBudgetCheck,
>         refillBudgetCheckRoundRobin, updateSchedContext, emptyRefill,
>         isCurDomainExpired, refillUnblockCheck,ifCondRefillUnblockCheck,
>         readRefillReady, refillReady, tcbReleaseEnqueue, tcbQueueRemove,
>         refillSufficient, readRefillSufficient, getRefillSufficient, postpone,
>         schedContextDonate, maybeDonateSc, maybeReturnSc, schedContextUnbindNtfn,
>         schedContextMaybeUnbindNtfn, isRoundRobin, getRefills, setRefills, getRefillFull,
>         schedContextCompleteYieldTo, schedContextUnbindYieldFrom,
>         schedContextUnbindReply, schedContextSetInactive, unbindFromSC,
>         schedContextCancelYieldTo, refillAbsoluteMax, schedContextUpdateConsumed,
>         scReleased, setConsumed, refillResetRR, preemptionPoint, refillHdInsufficient,
>         mergeNonoverlappingHeadRefill, headInsufficientLoop, maxReleaseTime, readScActive, scActive
>     ) where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Config
> import SEL4.Machine.Hardware
> import SEL4.Machine.RegisterSet(PPtr(..), Word)
> import SEL4.API.Failures(SyscallError(..))
> import SEL4.API.Types(MessageInfo(..))
> import SEL4.API.Types.Universal (schedContextSporadicFlag)
> import {-# SOURCE #-} SEL4.Kernel.VSpace(lookupIPCBuffer)
> import SEL4.Model.Failures
> import SEL4.Model.Preemption(KernelP, withoutPreemption)
> import SEL4.Model.PSpace(getObject, readObject, setObject)
> import SEL4.Model.StateData
> import SEL4.Model.Preemption
> import {-# SOURCE #-} SEL4.Object.Notification
> import {-# SOURCE #-} SEL4.Object.Reply
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB(threadGet, threadSet, checkBudget, chargeBudget, updateAt, setTimeArg, setMessageInfo, setMRs, threadRead)
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

> readSchedContext :: PPtr SchedContext -> KernelR SchedContext
> readSchedContext = readObject

> getSchedContext :: PPtr SchedContext -> Kernel SchedContext
> getSchedContext = getObject

> setSchedContext :: PPtr SchedContext -> SchedContext -> Kernel ()
> setSchedContext = setObject

> updateSchedContext :: PPtr SchedContext -> (SchedContext -> SchedContext) -> Kernel ()
> updateSchedContext scPtr f = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (f sc)

> refillIndex :: Int -> SchedContext -> Refill
> refillIndex index sc = scRefills sc !! index

> readRefillIndex :: PPtr SchedContext -> Int -> KernelR Refill
> readRefillIndex scPtr index = do
>     sc <- readSchedContext scPtr
>     return $ refillIndex index sc

> updateRefillIndex :: PPtr SchedContext -> (Refill -> Refill) -> Int -> Kernel ()
> updateRefillIndex scPtr f idx = updateSchedContext scPtr (\sc -> sc { scRefills = updateAt idx (scRefills sc) f})

> refillHd :: SchedContext -> Refill
> refillHd sc = scRefills sc !! scRefillHead sc

> readRefillHead :: PPtr SchedContext -> KernelR Refill
> readRefillHead scPtr = do
>     readStateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     readStateAssert (active_sc_at'_asrt scPtr) "there is an active scheduling context at scPtr"
>     sc <- readSchedContext scPtr
>     return $ refillHd sc

> getRefillHead :: PPtr SchedContext -> Kernel Refill
> getRefillHead scPtr = getsJust (readRefillHead scPtr)

> refillTl :: SchedContext -> Refill
> refillTl sc = scRefills sc !! scRefillTail sc

> readRefillTail :: PPtr SchedContext -> KernelR Refill
> readRefillTail scPtr = do
>     readStateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     readStateAssert (active_sc_at'_asrt scPtr) "there is an active scheduling context at scPtr"
>     sc <- readSchedContext scPtr
>     return $ refillTl sc

> getRefillTail :: PPtr SchedContext -> Kernel Refill
> getRefillTail scPtr = getsJust (readRefillTail scPtr)

> updateRefillHd :: PPtr SchedContext -> (Refill -> Refill) -> Kernel ()
> updateRefillHd scPtr f = updateSchedContext scPtr (\sc -> sc { scRefills = updateAt (scRefillHead sc) (scRefills sc) f})

> setRefillHd :: PPtr SchedContext -> Refill -> Kernel ()
> setRefillHd scPtr new = updateRefillHd scPtr (\r -> new)

> updateRefillTl :: PPtr SchedContext -> (Refill -> Refill) -> Kernel ()
> updateRefillTl scPtr f = updateSchedContext scPtr (\sc -> sc { scRefills = updateAt (scRefillTail sc) (scRefills sc) f})

> setRefillTl :: PPtr SchedContext -> Refill -> Kernel ()
> setRefillTl scPtr new = updateRefillTl scPtr (\r -> new)

> getRefills :: PPtr SchedContext -> Kernel [Refill]
> getRefills scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefills sc

> setRefills :: PPtr SchedContext -> [Refill] -> Kernel ()
> setRefills scPtr refills = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefills = refills })

> readScActive :: PPtr SchedContext -> KernelR Bool
> readScActive scPtr = do
>     sc <- readSchedContext scPtr
>     return $ scRefillMax sc > 0

> scActive :: PPtr SchedContext -> Kernel Bool
> scActive scPtr = getsJust (readScActive scPtr)

> readScReleased :: PPtr SchedContext -> KernelR Bool
> readScReleased scPtr = do
>     active <- readScActive scPtr
>     if active
>         then readRefillReady scPtr
>         else return False

> scReleased :: PPtr SchedContext -> Kernel Bool
> scReleased scPtr = getsJust (readScReleased scPtr)

> readRefillSingle :: PPtr SchedContext -> KernelR Bool
> readRefillSingle scPtr = do
>     sc <- readSchedContext scPtr
>     return $ scRefillHead sc == scRefillTail sc

> refillSingle :: PPtr SchedContext -> Kernel Bool
> refillSingle scPtr = getsJust (readRefillSingle scPtr)

> refillSize :: SchedContext -> Int
> refillSize sc =
>     if scRefillHead sc <= scRefillTail sc
>         then scRefillTail sc - scRefillHead sc + 1
>         else scRefillTail sc + 1 + (scRefillMax sc - scRefillHead sc)

> readRefillSize :: PPtr SchedContext -> KernelR Int
> readRefillSize scPtr = do
>     sc <- readSchedContext scPtr
>     return $ refillSize sc

> getRefillSize :: PPtr SchedContext -> Kernel Int
> getRefillSize scPtr = getsJust (readRefillSize scPtr)

> readRefillFull :: PPtr SchedContext -> KernelR Bool
> readRefillFull scPtr = do
>     sc <- readSchedContext scPtr
>     size <- readRefillSize scPtr
>     return $ size == scRefillMax sc

> getRefillFull :: PPtr SchedContext -> Kernel Bool
> getRefillFull scPtr = getsJust (readRefillFull scPtr)

> refillNext :: SchedContext -> Int -> Int
> refillNext sc index = if index == scRefillMax sc - 1 then 0 else index + 1

> readRefillNext :: PPtr SchedContext -> Int -> KernelR Int
> readRefillNext scPtr index = do
>     readStateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     readStateAssert (active_sc_at'_asrt scPtr) "there is an active scheduling context at scPtr"
>     sc <- readSchedContext scPtr
>     return $ refillNext sc index

> getRefillNext :: PPtr SchedContext -> Int -> Kernel Int
> getRefillNext scPtr index = getsJust (readRefillNext scPtr index)

> updateRefillNext :: PPtr SchedContext -> (Refill -> Refill) -> Int -> Kernel ()
> updateRefillNext scPtr f index = do
>     updateSchedContext scPtr (\sc -> sc { scRefills = updateAt (refillNext sc index) (scRefills sc) f})

> -- Odd argument order plays well with `updateSchedContext`.
> setRefillIndex :: Int -> Refill -> SchedContext -> SchedContext
> setRefillIndex index refill sc =
>     sc { scRefills = updateAt index (scRefills sc) (\x -> refill) }

> refillCapacity :: Ticks -> Refill -> Ticks
> refillCapacity usage refill =
>     if rAmount refill < usage
>         then 0
>         else rAmount refill - usage

> readRefillCapacity :: PPtr SchedContext -> Ticks -> KernelR Ticks
> readRefillCapacity scPtr usage = do
>     readStateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     readStateAssert (active_sc_at'_asrt scPtr) "there is an active scheduling context at scPtr"
>     head <- readRefillHead scPtr
>     return $ refillCapacity usage head

> getRefillCapacity :: PPtr SchedContext -> Ticks -> Kernel Ticks
> getRefillCapacity scPtr usage = getsJust (readRefillCapacity scPtr usage)

> refillSufficient :: Ticks -> Refill -> Bool
> refillSufficient usage refill = minBudget <= refillCapacity usage refill

> readRefillSufficient :: PPtr SchedContext -> Ticks -> KernelR Bool
> readRefillSufficient scPtr usage = do
>     capacity <- readRefillCapacity scPtr usage
>     return $ minBudget <= capacity

> getRefillSufficient :: PPtr SchedContext -> Ticks -> Kernel Bool
> getRefillSufficient scPtr usage = getsJust (readRefillSufficient scPtr usage)

> refillPopHead :: PPtr SchedContext -> Kernel Refill
> refillPopHead scPtr = do
>     stateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     stateAssert (active_sc_at'_asrt scPtr) "there is an active scheduling context at scPtr"
>     head <- getRefillHead scPtr
>     sc <- getSchedContext scPtr
>     next <- getRefillNext scPtr (scRefillHead sc)
>     updateSchedContext scPtr $ \sc -> sc { scRefillHead = next }
>     return head

> refillAddTail :: PPtr SchedContext -> Refill -> Kernel ()
> refillAddTail scPtr refill = do
>     stateAssert (active_sc_at'_asrt scPtr) "there is an active scheduling context at scPtr"
>     size <- getRefillSize scPtr
>     sc <- getSchedContext scPtr
>     assert (size < scRefillMax sc) "cannot add beyond queue size"
>     next <- getRefillNext scPtr (scRefillTail sc)
>     updateSchedContext scPtr $ \sc -> sc { scRefillTail = next }
>     updateRefillIndex scPtr (\r -> refill) next

> maybeAddEmptyTail :: PPtr SchedContext -> Kernel ()
> maybeAddEmptyTail scPtr = do
>     roundRobin <- isRoundRobin scPtr
>     when roundRobin $ do
>         head <- getRefillHead scPtr
>         tail <- return $ (Refill { rTime = rTime head, rAmount = 0 })
>         refillAddTail scPtr tail

> refillNew :: PPtr SchedContext -> Int -> Ticks -> Ticks -> Kernel ()
> refillNew scPtr maxRefills budget period = do
>     curTime <- getCurTime
>     updateSchedContext scPtr (\sc -> sc { scPeriod = period })
>     updateSchedContext scPtr (\sc -> sc { scRefillHead = 0 })
>     updateSchedContext scPtr (\sc -> sc { scRefillTail = 0 })
>     updateSchedContext scPtr (\sc -> sc { scRefillMax = maxRefills })
>     updateRefillHd scPtr $ \r -> r { rAmount = budget }
>     updateRefillHd scPtr $ \r -> r { rTime = curTime }
>     maybeAddEmptyTail scPtr

> readRefillReady :: PPtr SchedContext -> KernelR Bool
> readRefillReady scPtr = do
>     readStateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     readStateAssert (active_sc_at'_asrt scPtr) "there is an active scheduling context at scPtr"
>     head <- readRefillHead scPtr
>     curTime <- readCurTime
>     return $ rTime head <= curTime

> refillReady :: PPtr SchedContext -> Kernel Bool
> refillReady scPtr = getsJust (readRefillReady scPtr)

> refillUpdate :: PPtr SchedContext -> Ticks -> Ticks -> Int -> Kernel ()
> refillUpdate scPtr newPeriod newBudget newMaxRefills = do
>     updateSchedContext scPtr $ \sc -> sc { scRefills = updateAt 0 (scRefills sc) (\r -> refillHd sc) }
>     updateSchedContext scPtr (\sc -> sc { scRefillHead = 0 })
>     updateSchedContext scPtr (\sc -> sc { scRefillTail = scRefillHead sc })
>     updateSchedContext scPtr (\sc -> sc { scRefillMax = newMaxRefills })
>     updateSchedContext scPtr (\sc -> sc { scPeriod = newPeriod })
>     whenM (refillReady scPtr) $ do
>         curTime <- getCurTime
>         updateRefillHd scPtr $ \r -> r { rTime = curTime }
>     head <- getRefillHead scPtr
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
>     active <- scActive scPtr
>     assert active "scPtr should be active"
>     tail <- getRefillTail scPtr
>     if rTime tail + rAmount tail >= rTime new
>         then updateRefillTl scPtr (\last -> last { rAmount = rAmount tail + rAmount new })
>         else do
>           full <- getRefillFull scPtr
>           if not full
>              then refillAddTail scPtr new
>              else do
>                updateRefillTl scPtr (\last -> last { rTime = rTime new - rAmount tail})
>                updateRefillTl scPtr (\last -> last { rAmount = rAmount tail + rAmount new})

> refillResetRR :: PPtr SchedContext -> Kernel ()
> refillResetRR scPtr = do
>     head <- getRefillHead scPtr
>     tail <- getRefillTail scPtr
>     updateRefillHd scPtr (\hd -> hd { rAmount = rAmount head + rAmount tail})
>     updateRefillTl scPtr (\tl -> tl { rAmount = 0})

> refillHdInsufficient :: PPtr SchedContext -> KernelR Bool
> refillHdInsufficient scPtr = do
>     head <- readRefillHead scPtr
>     return $ rAmount head < minBudget

> mergeNonoverlappingHeadRefill :: PPtr SchedContext -> Kernel ()
> mergeNonoverlappingHeadRefill scPtr = do
>     old_head <- refillPopHead scPtr
>     updateRefillHd scPtr $ \head -> head { rAmount = rAmount head + rAmount old_head }
>     updateRefillHd scPtr $ \head -> head { rTime = rTime head - rAmount old_head}

> headInsufficientLoop :: PPtr SchedContext -> Kernel ()
> headInsufficientLoop scPtr = whileLoop (const (fromJust . runReaderT (refillHdInsufficient scPtr))) (const (mergeNonoverlappingHeadRefill scPtr)) ()

> mergeOverlappingRefills :: PPtr SchedContext -> Kernel ()
> mergeOverlappingRefills scPtr = do
>     old_head <- refillPopHead scPtr
>     updateRefillHd scPtr $ \head -> head { rTime = rTime old_head }
>     updateRefillHd scPtr $ \head -> head { rAmount = rAmount head + rAmount old_head }

> refillHeadOverlapping :: PPtr SchedContext -> KernelR Bool
> refillHeadOverlapping scPtr = do
>     single <- readRefillSingle scPtr
>     if not single
>         then do
>             head <- readRefillHead scPtr
>             sc <- readSchedContext scPtr
>             nextIndex <- readRefillNext scPtr (scRefillHead sc)
>             nextRefill <- readRefillIndex scPtr nextIndex
>             return $ rTime nextRefill <= rTime head + rAmount head
>         else return False

> refillHeadOverlappingLoop :: PPtr SchedContext -> Kernel ()
> refillHeadOverlappingLoop scPtr =
>     whileLoop (const (fromJust . runReaderT (refillHeadOverlapping scPtr))) (const (mergeOverlappingRefills scPtr)) ()

> maxReleaseTime :: Word64
> maxReleaseTime = (maxBound :: Word64) - 5 * usToTicks maxPeriodUs

> headRefillOverrun :: PPtr SchedContext -> Ticks -> KernelR Bool
> headRefillOverrun scPtr usage = do
>     head <- readRefillHead scPtr
>     return $ rAmount head <= usage && rTime head < maxReleaseTime

> chargeEntireHeadRefill :: PPtr SchedContext -> Ticks -> Kernel Ticks
> chargeEntireHeadRefill scPtr usage = do
>     head <- getRefillHead scPtr
>     sc <- getSchedContext scPtr
>     single <- refillSingle scPtr
>     if single
>        then updateRefillHd scPtr $ \r -> r { rTime = rTime head + scPeriod sc}
>        else do
>          old_head <- refillPopHead scPtr
>          let new = old_head { rTime = rTime old_head + scPeriod sc}
>          scheduleUsed scPtr new
>     return (usage - rAmount head)

> handleOverrun :: PPtr SchedContext -> Ticks -> Kernel Ticks
> handleOverrun scPtr usage =
>     whileLoop (\usage -> fromJust . runReaderT (headRefillOverrun scPtr usage)) (\usage -> chargeEntireHeadRefill scPtr usage) usage

> refillBudgetCheck :: Ticks -> Kernel ()
> refillBudgetCheck usage = do
>     scPtr <- getCurSc

>     active <- scActive scPtr
>     assert active "CurSc should be active"

>     roundRobin <- isRoundRobin scPtr
>     assert (not roundRobin) "the current sc should not be round robin when this function is called"

>     usage' <- handleOverrun scPtr usage

>     head <- getRefillHead scPtr

>     when (usage' > 0 && rTime head < maxReleaseTime) $ do
>       sc <- getSchedContext scPtr
>       used <- return Refill { rTime = rTime head + (scPeriod sc),
>                               rAmount = usage'}
>       updateRefillHd scPtr $ \r -> r { rAmount = rAmount head - usage' }
>       updateRefillHd scPtr $ \r -> r { rTime = rTime head + usage' }
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
>       stateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>       active <- scActive scPtr
>       assert active "the scheduling context must be active"
>       roundRobin <- isRoundRobin scPtr
>       ready <- refillReady scPtr
>       when ((not roundRobin) && ready) $ do
>         curTime <- getCurTime
>         updateRefillHd scPtr $ \head -> head { rTime = curTime }
>         setReprogramTimer True
>         refillHeadOverlappingLoop scPtr

> ifCondRefillUnblockCheck :: Maybe (PPtr SchedContext) -> Maybe Bool -> Maybe Bool -> Kernel ()
> ifCondRefillUnblockCheck scOpt act ast = do
>       when (scOpt /= Nothing) $ do
>           scPtr <- return $ fromJust scOpt
>           sc <- getSchedContext scPtr
>           curScPtr <- getCurSc
>           guard <- return $ (case act of
>                        Nothing -> not $ scSporadic sc
>                        Just True -> scSporadic sc && 0 < scRefillMax sc
>                        Just False -> scSporadic sc)
>           when (guard && (if ast == Just False then scPtr /= curScPtr else True)) $
>               when (if ast == Just True then scPtr /= curScPtr else True) $ refillUnblockCheck scPtr

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
>     stateAssert cur_tcb'_asrt
>         "Assert that `cur_tcb' s` holds"
>     consumed <- schedContextUpdateConsumed scPtr
>     tptr <- getCurThread
>     sent <- setMRs tptr buffer (setTimeArg consumed)
>     setMessageInfo tptr $ MI sent 0 0 0

> schedContextBindTCB :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextBindTCB scPtr tcbPtr = do
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr
>     updateSchedContext scPtr (\sc -> sc { scTCB = Just tcbPtr })
>     ifCondRefillUnblockCheck (Just scPtr) (Just True) (Just False)
>     schedContextResume scPtr
>     schedulable <- getSchedulable tcbPtr
>     when schedulable $ do
>         tcbSchedEnqueue tcbPtr
>         rescheduleRequired

> schedContextBindNtfn :: PPtr SchedContext -> PPtr Notification -> Kernel ()
> schedContextBindNtfn scPtr ntfnPtr = do
>     stateAssert sym_refs_asrt "Assert that `sym_refs (state_refs_of' s)` holds"
>     ntfn <- getNotification ntfnPtr
>     setNotification ntfnPtr (ntfn { ntfnSc = Just scPtr })
>     updateSchedContext scPtr (\sc -> sc { scNtfn = Just ntfnPtr })

> schedContextUnbindTCB :: PPtr SchedContext -> Kernel ()
> schedContextUnbindTCB scPtr = do
>     stateAssert sym_refs_asrt "Assert that `sym_refs (state_refs_of' s)` holds"
>     stateAssert valid_idle'_asrt
>         "Assert that `valid_idle' s` holds"
>     stateAssert cur_tcb'_asrt
>         "Assert that `cur_tcb' s` holds"
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
>     stateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     scPtrOpt <- threadGet tcbYieldTo tptr
>     when (scPtrOpt /= Nothing) $ do
>         scPtr <- return $ fromJust scPtrOpt
>         updateSchedContext scPtr (\sc -> sc { scYieldFrom = Nothing })
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

> schedContextSetInactive :: PPtr SchedContext -> Kernel ()
> schedContextSetInactive scPtr = do
>     updateSchedContext scPtr $ (\sc -> sc { scRefillMax = 0 })
>     updateSchedContext scPtr $ (\sc -> sc { scSporadic = False })

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
>     stateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     sc <- getSchedContext scPtr
>     assert (scTCB sc /= Nothing) "the sc must have an associated tcb"
>     tptr <- return $ fromJust $ scTCB sc
>     tcbSchedDequeue tptr
>     tcbReleaseEnqueue tptr
>     setReprogramTimer True

> schedContextResume :: PPtr SchedContext -> Kernel ()
> schedContextResume scPtr = do
>     stateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     sc <- getSchedContext scPtr
>     tptrOpt <- return $ scTCB sc
>     assert (tptrOpt /= Nothing) "schedContextResume: option of TCB pointer must not be Nothing"
>     tptr <- return $ fromJust tptrOpt
>     schedulable <- getSchedulable tptr
>     when schedulable $ do
>         ready <- refillReady scPtr
>         sufficient <- getRefillSufficient scPtr 0
>         when (not (ready && sufficient)) $ postpone scPtr

> contextYieldToUpdateQueues :: PPtr SchedContext -> Kernel Bool
> contextYieldToUpdateQueues scPtr = do
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTCB sc
>     schedulable <- getSchedulable tptr
>     if schedulable
>         then do
>             ctPtr <- getCurThread
>             prio <- threadGet tcbPriority tptr
>             curprio <- threadGet tcbPriority ctPtr
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
>         schedContextUnbindReply scPtr
>     InvokeSchedContextYieldTo scPtr buffer -> do
>         schedContextYieldTo scPtr buffer

> schedContextDonate :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextDonate scPtr tcbPtr = do
>     stateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     sc <- getSchedContext scPtr
>     fromOpt <- return $ scTCB sc
>     when (fromOpt /= Nothing) $ do
>         from <- return $ fromJust fromOpt
>         tcbSchedDequeue from
>         tcbReleaseRemove from
>         threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) from
>         cur <- getCurThread
>         action <- getSchedulerAction
>         when (from == cur || action == SwitchToThread from)
>             rescheduleRequired
>     updateSchedContext scPtr (\sc -> sc { scTCB = Just tcbPtr })
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr

> invokeSchedControlConfigureFlags :: SchedControlInvocation -> Kernel ()
> invokeSchedControlConfigureFlags iv = case iv of
>     InvokeSchedControlConfigureFlags scPtr budget period mRefills badge flags -> do
>         sc <- getSchedContext scPtr
>         when (scTCB sc /= Nothing) $ do
>             tcbReleaseRemove $ fromJust $ scTCB sc
>             tcbSchedDequeue $ fromJust $ scTCB sc
>             curSc <- getCurSc
>             when (curSc == scPtr) $ commitTime

>         if period == budget
>            then refillNew scPtr minRefills budget 0
>            else do
>                active <- scActive scPtr
>                if (active && scTCB sc /= Nothing)
>                    then do
>                      runnable <- isRunnable $ fromJust $ scTCB sc
>                      if runnable
>                         then refillUpdate scPtr period budget mRefills
>                         else refillNew scPtr mRefills budget period
>                    else refillNew scPtr mRefills budget period

>         when (scTCB sc /= Nothing) $ do
>             schedContextResume scPtr
>             runnable <- isRunnable $ fromJust $ scTCB sc
>             ctPtr <- getCurThread
>             if (fromJust $ scTCB sc) == ctPtr
>                 then rescheduleRequired
>                 else when runnable $ possibleSwitchTo $ fromJust $ scTCB sc

>         updateSchedContext scPtr (\sc -> sc { scBadge = badge })
>         updateSchedContext scPtr (\sc -> sc { scSporadic = flags `testBit` schedContextSporadicFlag })

> isRoundRobin :: PPtr SchedContext -> Kernel Bool
> isRoundRobin scPtr = do
>     sc <- getSchedContext scPtr
>     return (scPeriod sc == 0)

> isCurDomainExpired :: Kernel Bool
> isCurDomainExpired = do
>     domainTime <- getDomainTime
>     return $ 1 < numDomains && domainTime == 0

> commitTime :: Kernel ()
> commitTime = do
>     scPtr <- getCurSc
>     active <- scActive scPtr
>     idleSCPtr <- getIdleSC
>     when (active && idleSCPtr /= scPtr) $ do
>       consumed <- getConsumedTime
>       when (consumed > 0) $ do
>         ifM (isRoundRobin scPtr)
>           (refillBudgetCheckRoundRobin consumed)
>           (refillBudgetCheck consumed)
>       updateSchedContext scPtr $ \sc -> sc { scConsumed = scConsumed sc + consumed }
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
>     domainTime <- getDomainTime
>     when (numDomains > 1) $ if (curTime' - prevTime + minBudget >= domainTime)
>                             then setDomainTime 0
>                             else setDomainTime (domainTime - (curTime' - prevTime))

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
>         updateSchedContext scPtr (\sc -> sc { scTCB = Nothing })
>         cur <- getCurThread
>         when (tcbPtr == cur) rescheduleRequired

> readReadyTime :: PPtr SchedContext -> KernelR Time
> readReadyTime scPtr = do
>     head <- readRefillHead scPtr
>     return $ rTime head

> readTCBReadyTime :: PPtr TCB -> KernelR Time
> readTCBReadyTime tcbPtr = do
>     scPtrOpt <- threadRead tcbSchedContext tcbPtr
>     assert (scPtrOpt /= Nothing) "tcbPtr must have an associated scheduling context"
>     scPtr <- return $ fromJust scPtrOpt
>     active <- readScActive scPtr
>     assert active "the sc must be active"
>     readReadyTime (fromJust scPtrOpt)

> getTCBReadyTime :: PPtr TCB -> Kernel Time
> getTCBReadyTime tcbPtr = getsJust (readTCBReadyTime tcbPtr)

> timeAfter :: Maybe (PPtr TCB) -> Time -> KernelR Bool
> timeAfter tcbPtrOpt newTime = do
>     if (tcbPtrOpt /= Nothing)
>         then do
>           tcbPtr <- return $ fromJust tcbPtrOpt
>           time <- readTCBReadyTime (fromJust tcbPtrOpt)
>           return $ time <= newTime
>         else return False

> findTimeAfter :: Maybe (PPtr TCB) -> Time -> Kernel (Maybe (PPtr TCB))
> findTimeAfter tcbPtrOpt newTime = do
>     stateAssert tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt
>         "every thread in the release queue is associated with an active scheduling context"
>     whileLoop (\afterPtrOpt -> fromJust . runReaderT (timeAfter afterPtrOpt newTime))
>               (\afterPtrOpt -> do
>                   tcb <- getObject (fromJust afterPtrOpt)
>                   return $ tcbSchedNext tcb)
>               tcbPtrOpt

> tcbReleaseEnqueue :: PPtr TCB -> Kernel ()
> tcbReleaseEnqueue tcbPtr = do
>     stateAssert ready_or_release'_asrt
>         "Assert that `ready_or_release'` holds"
>     stateAssert (not_tcbQueued_asrt tcbPtr)
>         "tcbPtr must not have the tcbQueued flag set"
>     stateAssert ksReadyQueues_asrt ""
>     stateAssert ksReleaseQueue_asrt ""
>     stateAssert valid_objs'_asrt "assert that `valid_objs'` holds"
>     runnable <- isRunnable tcbPtr
>     assert runnable "thread must be runnable"
>     tcb <- getObject tcbPtr
>     assert (tcbInReleaseQueue tcb == False) "tcbPtr must not already be in the release queue"
>     newTime <- getTCBReadyTime tcbPtr
>     queue <- getReleaseQueue
>     ifM (orM (return (tcbQueueEmpty queue))
>              (do
>                headTime <- getTCBReadyTime (fromJust $ tcbQueueHead queue)
>                return (newTime < headTime)))
>         (do
>           newQueue <- tcbQueuePrepend queue tcbPtr
>           setReleaseQueue newQueue
>           setReprogramTimer True)
>         (do
>           assert (tcbQueueHead queue /= Nothing && tcbQueueEnd queue /= Nothing) "the queue is nonempty"
>           lastTime <- getTCBReadyTime (fromJust $ tcbQueueEnd queue)
>           if lastTime <= newTime
>               then do
>                   newQueue <- tcbQueueAppend queue tcbPtr
>                   setReleaseQueue newQueue
>               else do
>                   afterPtrOpt <- findTimeAfter (tcbQueueHead queue) newTime
>                   assert (afterPtrOpt /= Nothing) "the afterPtr must be in the queue"
>                   afterPtr <- return $ fromJust afterPtrOpt
>                   stateAssert (findTimeAfter_asrt afterPtr) "tcbPtr must be in the release queue"
>                   tcbQueueInsert tcbPtr afterPtr)
>     threadSet (\t -> t { tcbInReleaseQueue = True }) tcbPtr

In preemptible code, the kernel may explicitly mark a preemption point with the "preemptionPoint" function. The preemption will only be taken if an interrupt has occurred and the preemption point has been called "workUnitsLimit" times.

> workUnitsLimit = error "see Kernel_Config"

> preemptionPoint :: KernelP ()
> preemptionPoint = do
>     withoutPreemption $ modifyWorkUnits (\op -> op + 1)
>     workUnits <- withoutPreemption $ getWorkUnits
>     when (workUnitsLimit <= workUnits) $ do
>       withoutPreemption $ setWorkUnits 0
>       withoutPreemption $ updateTimeStamp
>       preempt <- withoutPreemption $ doMachineOp (getActiveIRQ True)
>       domExp <- withoutPreemption $ isCurDomainExpired
>       csc <- withoutPreemption $ getCurSc
>       stateAssert (sc_at'_asrt csc) "there is a scheduling context at ksCurSc"
>       consumed <- withoutPreemption $ getConsumedTime
>       test <- withoutPreemption $ andM (scActive csc) (getRefillSufficient csc consumed)
>       if (isJust preempt || domExp || not test)
>          then throwError ()
>          else return ()
