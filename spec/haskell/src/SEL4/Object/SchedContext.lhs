%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module specifies the behavior of schedule context objects.

\begin{impdetails}

This module uses the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.SchedContext (
>         schedContextUnbindAllTCBs, invokeSchedContext,
>         invokeSchedControlConfigure, getSchedContext,
>         schedContextUnbindTCB, schedContextBindTCB, schedContextResume,
>         setSchedContext, updateTimeStamp, commitTime, rollbackTime,
>         refillHd, refillTl, minBudget, minBudgetUs, refillCapacity, refillBudgetCheck,
>         refillSplitCheck, isCurDomainExpired, refillUnblockCheck,
>         refillReadyTCB, refillReady, tcbReleaseEnqueue,
>         guardedSwitchTo, refillSufficient, postpone,
>         schedContextDonate,
>         maybeDonateSc, maybeReturnSc,
>         schedContextMaybeUnbindNtfn, schedContextUnbindNtfn,
>         isRoundRobin, getRefills, setRefills, refillFull, refillAbsoluteMax,
>         schedContextCompleteYieldTo, schedContextCancelYieldTo,
>         schedContextUpdateConsumed, setConsumed
>     ) where

\begin{impdetails}

> import SEL4.Machine.Hardware
> import SEL4.Machine.RegisterSet(PPtr(..), Word)
> import SEL4.API.Failures(SyscallError(..))
> import SEL4.API.Types(MessageInfo(..))
> import {-# SOURCE #-} SEL4.Kernel.VSpace(lookupIPCBuffer)
> import SEL4.Model.Failures(KernelF, withoutFailure)
> import SEL4.Model.PSpace(getObject, setObject)
> import SEL4.Model.StateData
> import {-# SOURCE #-} SEL4.Object.Notification
> import {-# SOURCE #-} SEL4.Object.Reply
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB(threadGet, threadSet, checkBudget, chargeBudget, replaceAt, setTimeArg, setMessageInfo, setMRs)
> import {-# SOURCE #-} SEL4.Kernel.Thread
> import SEL4.API.Invocation(SchedContextInvocation(..), SchedControlInvocation(..))

> import Data.List(delete)
> import Data.Word(Word64)
> import Data.Maybe

\end{impdetails}

> minBudget :: Word64
> minBudget = 2 * kernelWCETTicks

> minBudgetUs :: Word64
> minBudgetUs = 2 * kernelWCETUs

> getTCBSc :: PPtr TCB -> Kernel SchedContext
> getTCBSc tcbPtr = do
>     scOpt <- threadGet tcbSchedContext tcbPtr
>     assert (scOpt /= Nothing) "getTCBSc: SchedContext pointer must not be Nothing" 
>     getSchedContext $ fromJust scOpt

> refillHd :: SchedContext -> Refill
> refillHd sc = (scRefills sc) !! (scRefillHead sc)

> refillTl :: SchedContext -> Refill
> refillTl sc = (scRefills sc) !! (scRefillTail sc)

> getScTime :: PPtr TCB -> Kernel Time
> getScTime tcbPtr = do
>     sc <- getTCBSc tcbPtr
>     return $ rTime (refillHd sc)

> tcbReleaseEnqueue :: PPtr TCB -> Kernel ()
> tcbReleaseEnqueue tcbPtr = do
>     time <- getScTime tcbPtr
>     qs <- getReleaseQueue
>     times <- mapM getScTime qs
>     qst <- return $ zip qs times
>     qst' <- return $ filter (\(_,t') -> t' <= time) qst ++ [(tcbPtr, time)] ++ filter (\(_,t') -> not (t' <= time)) qst
>     when (head qst /= head qst') $
>         setReprogramTimer True
>     setReleaseQueue (map fst qst')

> refillsCapacity :: Time -> [Refill] -> Int -> Time
> refillsCapacity usage refills headIndex =
>     if rAmount (refills !! headIndex) < usage
>         then 0
>         else rAmount (refills !! headIndex) - usage

> refillCapacity :: PPtr SchedContext -> Time -> Kernel Time
> refillCapacity scPtr usage = do
>     refills <- getRefills scPtr
>     sc <- getSchedContext scPtr
>     return $ refillsCapacity usage refills (scRefillHead sc)

> sufficientRefills :: Time -> [Refill] -> Int -> Bool
> sufficientRefills usage refills headIndex = minBudget <= refillsCapacity usage refills headIndex

> refillSufficient :: PPtr SchedContext -> Time -> Kernel Bool
> refillSufficient scPtr usage = do
>     refills <- getRefills scPtr
>     sc <- getSchedContext scPtr
>     return $ sufficientRefills usage refills (scRefillHead sc)

> getRefills :: PPtr SchedContext -> Kernel [Refill]
> getRefills scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefills sc

\subsection{Bind a TCB to a scheduling context}

> getSchedContext :: PPtr SchedContext -> Kernel SchedContext
> getSchedContext = getObject

> setSchedContext :: PPtr SchedContext -> SchedContext -> Kernel ()
> setSchedContext = setObject

> refillReady :: PPtr SchedContext -> Kernel Bool
> refillReady scPtr = do
>     curTime <- getCurTime
>     sc <- getSchedContext scPtr
>     scTime <- return $ rTime (refillHd sc)
>     return $ scTime <= curTime + kernelWCETTicks

> refillSize :: PPtr SchedContext -> Kernel Int
> refillSize scPtr = do
>     sc <- getSchedContext scPtr
>     if scRefillHead sc <= scRefillTail sc
>         then return $ scRefillTail sc - scRefillHead sc + 1
>         else return $ scRefillTail sc + 1 + (scRefillMax sc - scRefillHead sc)

> refillFull :: PPtr SchedContext -> Kernel Bool
> refillFull scPtr = do
>     sc <- getSchedContext scPtr
>     sz <- refillSize scPtr
>     return $ sz == scRefillMax sc

> refillSingle :: PPtr SchedContext -> Kernel Bool
> refillSingle scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefillHead sc == scRefillTail sc

> setRefills :: PPtr SchedContext -> [Refill] -> Kernel ()
> setRefills scPtr refills = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefills = refills })

> refillAddTail :: PPtr SchedContext -> Refill -> Kernel ()
> refillAddTail scPtr rfl = do
>     sc <- getSchedContext scPtr
>     refills <- return $ scRefills sc
>     size <- refillSize scPtr
>     assert (size < scRefillMax sc) "Length of Refill list must be less than the maximum"
>     newTail <- return $ if scRefillTail sc == scRefillMax sc - 1
>         then 0
>         else scRefillTail sc + 1
>     refills' <- return $ replaceAt newTail refills rfl
>     setSchedContext scPtr (sc { scRefills = refills', scRefillTail = newTail })

> maybeAddEmptyTail :: PPtr SchedContext -> Kernel ()
> maybeAddEmptyTail scPtr = do
>     robin <- isRoundRobin scPtr
>     when robin $ do
>         curTime <- getCurTime
>         refillAddTail scPtr (Refill { rTime = curTime, rAmount = 0 })

> refillNew :: PPtr SchedContext -> Int -> Ticks -> Ticks -> Kernel ()
> refillNew scPtr maxRefills budget period = do
>     sc <- getSchedContext scPtr
>     assert (minBudget < budget) "Budget must be greater than the minimum"
>     curTime <- getCurTime
>     refills <- return $ scRefills sc
>     refills' <- return $ replaceAt 0 refills (Refill { rTime = curTime, rAmount = budget })
>     sc' <- return $ sc { scPeriod = period,
>                          scRefills = refills',
>                          scRefillMax = maxRefills,
>                          scRefillHead = 0,
>                          scRefillTail = 0 }
>     setSchedContext scPtr sc'
>     maybeAddEmptyTail scPtr

> scheduleUsed :: PPtr SchedContext -> Refill -> Kernel ()
> scheduleUsed scPtr new = do
>     sc <- getSchedContext scPtr
>     refills <- getRefills scPtr
>     refillTail <- return $ refills !! (scRefillTail sc)
>     isSingle <- refillSingle scPtr
>     if (rAmount new < minBudget && not isSingle)
>         then do
>             refills' <- return $ replaceAt (scRefillTail sc) refills (refillTail { rAmount = rAmount refillTail + rAmount new,
>                             rTime = max (rTime new) (rTime refillTail)})
>             setRefills scPtr refills'
>         else
>             if (rTime new <= rTime refillTail)
>                 then do
>                     refills' <- return $ replaceAt (scRefillTail sc) refills (refillTail { rAmount = rAmount refillTail + rAmount new })
>                     setRefills scPtr refills'
>                 else do
>                     refillAddTail scPtr new

> mergeRefill :: Refill -> Refill -> Refill
> mergeRefill r1 r2 =
>     Refill { rTime = rTime r1, rAmount = rAmount r2 + rAmount r1 }

> canMergeRefill r1 r2 = rTime r2 <= rTime r1 + rAmount r1

> refillsMergePrefix :: [Refill] -> Int -> Int -> Int -> ([Refill], Int)
> refillsMergePrefix rs headIndex tailIndex total =
>     let headRefill = rs !! headIndex
>         nextRefill = rs !! ((headIndex + 1) `mod` total)
>     in if headIndex /= tailIndex && canMergeRefill headRefill nextRefill
>            then let rs' = replaceAt ((headIndex + 1) `mod` total) rs (mergeRefill headRefill nextRefill)
>                 in refillsMergePrefix rs' ((headIndex + 1) `mod` total) tailIndex total
>            else (rs, headIndex)

> refillUnblockCheck :: PPtr SchedContext -> Kernel ()
> refillUnblockCheck scPtr = do
>     robin <- isRoundRobin scPtr
>     when (not robin) $ do
>         ready <- refillReady scPtr
>         when ready $ do
>             sc <- getSchedContext scPtr
>             refills <- getRefills scPtr
>             hdRefill <- return $ refills !! (scRefillHead sc)
>             ct <- getCurTime
>             refills' <- return $ replaceAt (scRefillHead sc) refills (hdRefill { rTime = ct })
>             setReprogramTimer True
>             (refills'', headIndex) <- return $ refillsMergePrefix refills' (scRefillHead sc) (scRefillTail sc) (scRefillMax sc)
>             assert (sufficientRefills 0 refills'' headIndex) "refillUnblockCheck: error for sufficientRefills"
>             setSchedContext scPtr (sc { scRefills = refills'', scRefillHead = headIndex })

> minBudgetMerge :: PPtr SchedContext -> Kernel ()
> minBudgetMerge scPtr = do
>     sc <- getSchedContext scPtr
>     refills <- return $ scRefills sc
>     afterHeadIndex <- return $ if scRefillHead sc == scRefillMax sc - 1 then 0 else scRefillHead sc + 1
>     amount <- return $ rAmount (refills !! afterHeadIndex) + rAmount (refills !! scRefillHead sc)
>     refills' <- return $ replaceAt afterHeadIndex refills ((refills !! afterHeadIndex) { rAmount = amount })
>     setSchedContext scPtr (sc { scRefills = refills', scRefillHead = afterHeadIndex })
>     full <- refillFull scPtr
>     when (amount < minBudget || full) $ minBudgetMerge scPtr

> refillsBudgetCheck :: PPtr SchedContext -> Ticks -> Kernel Ticks
> refillsBudgetCheck scPtr usage = do
>     sc <- getSchedContext scPtr
>     refills <- getRefills scPtr
>     hdRefill <- return $ refillHd sc
>     if rAmount hdRefill <= usage
>         then do
>             single <- refillSingle scPtr
>             if single
>                 then do
>                     setRefills scPtr $ replaceAt (scRefillHead sc) refills (hdRefill { rTime = rTime hdRefill + scPeriod sc })
>                 else do
>                     setSchedContext scPtr (sc { scRefillHead = (scRefillHead sc + 1) `mod` (scRefillMax sc) })
>                     scheduleUsed scPtr (hdRefill { rTime = rTime hdRefill + scPeriod sc })
>             refillsBudgetCheck scPtr (usage - rAmount hdRefill)
>         else return usage

> refillBudgetCheck :: PPtr SchedContext -> Ticks -> Ticks -> Kernel ()
> refillBudgetCheck scPtr usage capacity = do
>     full <- refillFull scPtr
>     assert (capacity < minBudget || full) "refillBudgetCheck: this function should only be called when the sc is out of budget"
>     sc <- getSchedContext scPtr
>     period <- return $ scPeriod sc
>     assert (period > 0) "refillBudgetCheck: period must be greater than 0"

>     usage' <- (if (capacity == 0) then
>         refillsBudgetCheck scPtr usage
>         else return usage)
>     refills <- return $ scRefills sc

>     sc <- getSchedContext scPtr
>     when (capacity == 0 && 0 < usage') $
>         let r1 = refills !! (scRefillHead sc)
>             r1' = r1 { rTime = rTime r1 + usage' }
>             r2 = (if scRefillHead sc == scRefillMax sc - 1
>                       then head refills
>                       else refills !! (scRefillHead sc + 1))
>         in if scRefillHead sc /= scRefillTail sc && canMergeRefill r1' r2
>                then do
>                    refills' <- return $ replaceAt ((scRefillHead sc + 1) `mod` (scRefillMax sc)) refills (mergeRefill r1' r2)
>                    setSchedContext scPtr (sc { scRefills = refills', scRefillHead = (scRefillHead sc + 1) `mod` (scRefillMax sc) })
>                else do
>                    refills' <- return $ replaceAt (scRefillHead sc) refills r1'
>                    setRefills scPtr refills'

>     capacity <- refillCapacity scPtr usage'
>     ready <- refillReady scPtr
>     when (capacity > 0 && ready) $ refillSplitCheck scPtr usage'
>     full <- refillFull scPtr
>     sc' <- getSchedContext scPtr
>     when (rAmount (refillHd sc') < minBudget || full) $ minBudgetMerge scPtr

> refillSplitCheck :: PPtr SchedContext -> Time -> Kernel ()
> refillSplitCheck scPtr usage = do
>     ct <- getCurTime
>     sc <- getSchedContext scPtr
>     refills <- return $ scRefills sc
>     rfhd <- return $ refillHd sc
>     assert (0 < usage && usage <= rAmount rfhd) "Time usage must be within (0, rAmount of the refills head]"
>     assert (rTime rfhd <= ct) "rTime must not be greater than the current time"

>     remaining <- return $ rAmount rfhd - usage
>     new <- return (Refill { rTime = rTime rfhd + scPeriod sc, rAmount = usage })

>     size <- refillSize scPtr
>     if size == scRefillMax sc || remaining < minBudget
>         then if scRefillHead sc == scRefillTail sc
>                  then do
>                      refills' <- return $ replaceAt (scRefillHead sc) refills (new { rAmount = rAmount new + remaining })
>                      setRefills scPtr refills'
>                  else
>                      let r = refills !! ((scRefillHead sc + 1) `mod` (scRefillMax sc))
>                      in do
>                          refills' <- return $ replaceAt ((scRefillHead sc + 1) `mod` scRefillMax sc) refills
>                              (r { rAmount = rAmount r + remaining })
>                          setSchedContext scPtr (sc { scRefills = refills', scRefillHead = (scRefillHead sc + 1) `mod` scRefillMax sc })
>                          scheduleUsed scPtr new
>         else do
>             refills' <- return $ replaceAt (scRefillHead sc) refills (rfhd { rAmount = remaining, rTime = rTime rfhd + usage })
>             setRefills scPtr refills'
>             scheduleUsed scPtr new

> refillUpdate :: PPtr SchedContext -> Ticks -> Ticks -> Int -> Kernel ()
> refillUpdate scPtr newPeriod newBudget newMaxRefills = do
>     sc <- getSchedContext scPtr
>     assert (scRefillMax sc > 0) "refill must be initialised in order to be updated"
>     refills <- return $ scRefills sc
>     refills1 <- return $ replaceAt 0 refills (refills !! (scRefillHead sc))
>     sc1 <- return $ sc { scPeriod = newPeriod, scRefillHead = 0, scRefillTail = 0,
>         scRefills = refills1, scRefillMax = newMaxRefills }
>     setSchedContext scPtr sc1
>     curTime <- getCurTime
>     ready <- refillReady scPtr
>     refills2 <- if ready then return $ replaceAt 0 refills1 ((head refills1) { rTime = curTime })
>                 else return refills1
>     setRefills scPtr refills2
>     if (rAmount (head refills2) >= newBudget)
>         then do
>             refills3 <- return $ replaceAt 0 refills2 ((head refills2) { rAmount = newBudget })
>             setRefills scPtr refills3
>             maybeAddEmptyTail scPtr
>         else refillAddTail scPtr (Refill { rAmount = (newBudget - rAmount (head refills2)),
>                                            rTime = rTime (head refills2) + newPeriod })

> postpone :: PPtr SchedContext -> Kernel ()
> postpone scPtr = do
>     sc <- getSchedContext scPtr
>     tptrOpt <- return $ scTCB sc
>     assert (tptrOpt /= Nothing) "postpone: option of TCB pointer must not be Nothing"
>     tptr <- return $ fromJust tptrOpt
>     tcbSchedDequeue tptr
>     tcbReleaseEnqueue tptr
>     setReprogramTimer True

> schedContextResume :: PPtr SchedContext -> Kernel ()
> schedContextResume scPtr = do
>     sc <- getSchedContext scPtr
>     tptrOpt <- return $ scTCB sc
>     assert (tptrOpt /= Nothing) "schedContextResume: option of TCB pointer must not be Nothing"
>     tptr <- return $ fromJust tptrOpt
>     inRlsQueue <- inReleaseQueue tptr
>     sched <- isSchedulable tptr inRlsQueue
>     when sched $ do
>         ready <- refillReady scPtr
>         sufficient <- refillSufficient scPtr 0
>         runnable <- isRunnable tptr
>         when (runnable && 0 < scRefillMax sc && not (ready && sufficient)) $ postpone scPtr

> schedContextBindTCB :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextBindTCB scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr $ sc { scTCB = Just tcbPtr }
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr
>     schedContextResume scPtr
>     inq <- inReleaseQueue tcbPtr
>     sched <- isSchedulable tcbPtr inq
>     when sched $ possibleSwitchTo tcbPtr

> schedContextUnbindTCB :: PPtr SchedContext -> Kernel ()
> schedContextUnbindTCB scPtr = do
>     sc <- getSchedContext scPtr
>     let tptrOpt = scTCB sc
>     assert (tptrOpt /= Nothing) "schedContextUnbind: option of TCB pointer must not be Nothing"
>     let tptr = fromJust tptrOpt
>     tcbSchedDequeue tptr
>     tcbReleaseRemove tptr
>     threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tptr
>     setSchedContext scPtr $ sc { scTCB = Nothing }
>     cur <- getCurThread
>     when (tptr == cur) $ rescheduleRequired

> schedContextDonate :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextDonate scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     fromOpt <- return $ scTCB sc
>     when (fromOpt /= Nothing) $ do
>         cur <- getCurThread
>         from <- return $ fromJust fromOpt
>         if (from == cur)
>             then rescheduleRequired
>             else do
>                 runnable <- isRunnable from
>                 when runnable $ tcbSchedDequeue from
>         threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) from
>     setSchedContext scPtr (sc { scTCB = Just tcbPtr })
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr

> schedContextUnbindAllTCBs :: PPtr SchedContext -> Kernel ()
> schedContextUnbindAllTCBs scPtr = do
>     sc <- getSchedContext scPtr
>     when (scTCB sc /= Nothing) $ schedContextUnbindTCB scPtr

> schedContextUpdateConsumed :: PPtr SchedContext -> Kernel Word64
> schedContextUpdateConsumed scPtr = do
>     sc <- getSchedContext scPtr
>     consumed <- return $ scConsumed sc
>     if (consumed >= maxTicksToUs)
>         then do
>             setSchedContext scPtr $ sc { scConsumed = scConsumed sc - maxTicksToUs }
>             return maxTicksToUs
>         else do
>             setSchedContext scPtr $ sc { scConsumed = 0 }
>             return $ ticksToUs consumed

> schedContextYieldTo :: PPtr SchedContext -> [Word] -> Kernel ()
> schedContextYieldTo scPtr buffer = do
>     refillUnblockCheck scPtr
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTCB sc
>     inq <- inReleaseQueue tptr
>     schedulable <- isSchedulable tptr inq
>     if schedulable
>         then do
>             sufficient <- refillSufficient scPtr 0
>             ready <- refillReady scPtr
>             assert (sufficient && ready) "schedContextYieldTo: refill must be sufficient and ready"
>             ctPtr <- getCurThread
>             threadSet (\tcb -> tcb { tcbYieldTo = Just scPtr }) ctPtr
>             setSchedContext scPtr (sc { scYieldFrom = Just ctPtr })
>             possibleSwitchTo $ fromJust $ scTCB sc
>         else setConsumed scPtr (PPtr (head buffer))

> setConsumed :: PPtr SchedContext -> PPtr Word -> Kernel ()
> setConsumed scPtr buffer = do
>     consumed <- schedContextUpdateConsumed scPtr
>     tptr <- getCurThread
>     sent <- setMRs tptr (Just buffer) (setTimeArg consumed)
>     setMessageInfo tptr $ MI sent 0 0 0

> invokeSchedContext :: SchedContextInvocation -> KernelF SyscallError ()
> invokeSchedContext iv = withoutFailure $ case iv of
>     InvokeSchedContextConsumed scPtr buffer -> setConsumed scPtr (PPtr (head buffer))
>     InvokeSchedContextBind scPtr cap -> case cap of
>         ThreadCap tcbPtr -> schedContextBindTCB scPtr tcbPtr
>         NotificationCap ntfnPtr _ _ _ -> schedContextBindNtfn scPtr ntfnPtr
>         _ -> fail "invokeSchedContext: cap must be ThreadCap or NotificationCap"
>     InvokeSchedContextUnbindObject scPtr cap -> case cap of
>         ThreadCap _ -> schedContextUnbindTCB scPtr
>         NotificationCap _ _ _ _ -> schedContextUnbindNtfn scPtr
>         _ -> fail "invokeSchedContext: cap must be ThreadCap or NotificationCap"
>     InvokeSchedContextUnbind scPtr -> do
>         schedContextUnbindAllTCBs scPtr
>         schedContextUnbindNtfn scPtr
>     InvokeSchedContextYieldTo scPtr buffer -> do
>         schedContextYieldTo scPtr buffer

> invokeSchedControlConfigure :: SchedControlInvocation -> KernelF SyscallError ()
> invokeSchedControlConfigure iv = case iv of
>     InvokeSchedControlConfigure scPtr budget period mRefills badge -> withoutFailure $ do
>         sc <- getSchedContext scPtr
>         let tptrOpt = scTCB sc
>         setSchedContext scPtr $ sc { scBadge = badge }
>         when (tptrOpt /= Nothing) $ do
>             let tptr = fromJust tptrOpt
>             tcbReleaseRemove tptr
>             tcbSchedDequeue tptr
>             curSc <- getCurSc
>             when (curSc == scPtr) $ do
>                 consumed <- getConsumedTime
>                 capacity <- refillCapacity scPtr consumed
>                 budgetEnough <- checkBudget
>                 if budgetEnough
>                     then commitTime
>                     else chargeBudget capacity consumed False
>             let (period, mRefills) = if budget == period then (0, minRefills) else (period, mRefills)
>             runnable <- isRunnable tptr
>             if scRefillMax sc > 0 && runnable
>                 then refillUpdate scPtr period budget mRefills
>                 else refillNew scPtr mRefills budget period
>             when (scRefillMax sc > 0) $ do
>                 schedContextResume scPtr
>                 ctPtr <- getCurThread
>                 if (tptr == ctPtr)
>                     then rescheduleRequired
>                     else when runnable $ possibleSwitchTo tptr

> isCurDomainExpired :: Kernel Bool
> isCurDomainExpired = do
>     domainTime <- getDomainTime
>     consumedTime <- getConsumedTime
>     return $! domainTime < consumedTime + minBudget

> isRoundRobin :: PPtr SchedContext -> Kernel Bool
> isRoundRobin scPtr = do
>     sc <- getSchedContext scPtr
>     return (scPeriod sc == 0)

> commitDomainTime :: Kernel ()
> commitDomainTime = do
>     domainTime <- getDomainTime
>     consumed <- getConsumedTime
>     time' <- return (if domainTime < consumed then 0 else domainTime - consumed)
>     setDomainTime time'

> commitTime :: Kernel ()
> commitTime = do
>     consumed <- getConsumedTime
>     scPtr <- getCurSc
>     sc <- getSchedContext scPtr
>     when (0 < consumed) $ do
>         robin <- isRoundRobin scPtr
>         if robin
>             then do
>                 refills <- getRefills scPtr
>                 let newHd = (refillHd sc) { rAmount = rAmount (refillHd sc) - consumed }
>                     newTl = (refillTl sc) { rAmount = rAmount (refillTl sc) + consumed }
>                     refills' = replaceAt (scRefillHead sc) refills newHd
>                     refills'' = replaceAt (scRefillTail sc) refills' newTl
>                 setRefills scPtr refills''
>             else refillSplitCheck scPtr consumed
>     commitDomainTime
>     sc' <- getSchedContext scPtr
>     setSchedContext scPtr (sc' { scConsumed = scConsumed sc' + consumed })
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
>     setConsumedTime (curTime' - prevTime)

> refillReadyTCB :: PPtr TCB -> Kernel Bool
> refillReadyTCB tptr = do
>     scOpt <- threadGet tcbSchedContext tptr
>     assert (scOpt /= Nothing) "refillReadyTCB: scOpt must not be Nothing"
>     scPtr <- return (fromJust scOpt)
>     refillReady scPtr

> guardedSwitchTo :: PPtr TCB -> Kernel ()
> guardedSwitchTo tptr = do
>     inq <- inReleaseQueue tptr
>     sched <- isSchedulable tptr inq
>     assert sched "guardedSwitchTo: thread must be schedulable"
>     switchToThread tptr

> schedContextBindNtfn :: PPtr SchedContext -> PPtr Notification -> Kernel ()
> schedContextBindNtfn sc ntfn = do
>     n <- getNotification ntfn
>     setNotification ntfn (n { ntfnSc = Just sc })
>     s <- getSchedContext sc
>     setSchedContext sc (s { scNtfn = Just ntfn })

> schedContextUnbindNtfn :: PPtr SchedContext -> Kernel ()
> schedContextUnbindNtfn scPtr = do
>     sc <- getSchedContext scPtr
>     case scNtfn sc of
>         Nothing -> return ()
>         Just ntfnPtr -> (\ntfn -> do
>             setSchedContext scPtr (sc { scNtfn = Nothing })
>             n <- getNotification ntfn
>             setNotification ntfn (n { ntfnSc = Nothing })) ntfnPtr

> schedContextMaybeUnbindNtfn :: PPtr Notification -> Kernel ()
> schedContextMaybeUnbindNtfn ntfnPtr = do
>     scOpt <- liftM ntfnSc $ getNotification ntfnPtr
>     case scOpt of
>         Nothing -> return ()
>         Just sc -> schedContextUnbindNtfn sc

> maybeDonateSc :: PPtr TCB -> PPtr Notification -> Kernel ()
> maybeDonateSc tcbPtr ntfnPtr = do
>     scOpt <- threadGet tcbSchedContext tcbPtr
>     when (scOpt == Nothing) $ do
>         scPtrOpt <- liftM ntfnSc (getNotification ntfnPtr)
>         case scPtrOpt of
>             Nothing -> return ()
>             Just scPtr -> do
>                 scTCB <- liftM scTCB $ getSchedContext scPtr
>                 when (scTCB == Nothing) $ schedContextDonate scPtr tcbPtr

> maybeReturnSc :: PPtr Notification -> PPtr TCB -> Kernel ()
> maybeReturnSc ntfnPtr tcbPtr = do
>     nscOpt <- liftM ntfnSc $ getNotification ntfnPtr
>     tscOpt <- threadGet tcbSchedContext tcbPtr
>     when (nscOpt == tscOpt && nscOpt /= Nothing) $ do
>         assert (nscOpt /= Nothing) "maybeReturnSc: nscOpt must not be Nothing"
>         scPtr <- return $ fromJust nscOpt
>         threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tcbPtr
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scTCB = Nothing })

> coreSchedContextBytes :: Int
> coreSchedContextBytes = 88

> refillSizeBytes :: Int
> refillSizeBytes = 16

> refillAbsoluteMax :: Capability -> Int
> refillAbsoluteMax (SchedContextCap _ sc) = (sc - coreSchedContextBytes) `div` refillSizeBytes + minRefills
> refillAbsoluteMax _ = 0

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
>         case bufferOpt of
>             Nothing -> fail "schedContextCompleteYieldTo: buffer must not be Nothing"
>             Just buffer -> do
>                 setConsumed scPtr buffer
>                 schedContextCancelYieldTo tptr
>                 setThreadState Running tptr

