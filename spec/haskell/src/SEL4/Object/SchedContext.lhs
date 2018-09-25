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
>         schedContextUpdateConsumed, setConsumed, schedContextUnbindReply,
>         getTCBSc
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
> import {-# SOURCE #-} SEL4.Object.TCB(threadGet, threadSet, checkBudget, chargeBudget, setTimeArg, setMessageInfo, setMRs)
> import {-# SOURCE #-} SEL4.Kernel.Thread
> import SEL4.API.Invocation(SchedContextInvocation(..), SchedControlInvocation(..))

> import Data.Bits
> import Data.List(delete)
> import Data.Word(Word64)
> import Data.Maybe

\end{impdetails}

> minBudget :: Word64
> minBudget = 2 * kernelWCET_ticks

> minBudgetUs :: Word64
> minBudgetUs = 2 * kernelWCET_us

> getTCBSc :: PPtr TCB -> Kernel SchedContext
> getTCBSc tcbPtr = do
>     scOpt <- threadGet tcbSchedContext tcbPtr
>     assert (scOpt /= Nothing) "getTCBSc: SchedContext pointer must not be Nothing"
>     getSchedContext $ fromJust scOpt

> refillHd :: SchedContext -> Refill
> refillHd sc = head (scRefills sc)

> refillTl :: SchedContext -> Refill
> refillTl sc = last (scRefills sc)

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

> refillsCapacity :: Time -> [Refill] -> Time
> refillsCapacity usage refills =
>     if rAmount (head refills) < usage
>         then 0
>         else rAmount (head refills) - usage

> refillCapacity :: PPtr SchedContext -> Time -> Kernel Time
> refillCapacity scPtr usage = do
>     refills <- getRefills scPtr
>     return $ refillsCapacity usage refills

> sufficientRefills :: Time -> [Refill] -> Bool
> sufficientRefills usage refills = minBudget <= refillsCapacity usage refills

> refillSufficient :: PPtr SchedContext -> Time -> Kernel Bool
> refillSufficient scPtr usage = do
>     refills <- getRefills scPtr
>     return $ sufficientRefills usage refills

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
>     return $ scTime <= curTime + kernelWCET_ticks

> refillSize :: PPtr SchedContext -> Kernel Int
> refillSize scPtr = do
>     refills <- getRefills scPtr
>     return $ length refills

> refillFull :: PPtr SchedContext -> Kernel Bool
> refillFull scPtr = do
>     sc <- getSchedContext scPtr
>     sz <- refillSize scPtr
>     return $ sz == scRefillMax sc

> refillSingle :: PPtr SchedContext -> Kernel Bool
> refillSingle scPtr = do
>     sz <- refillSize scPtr
>     return $ sz == 1

> setRefills :: PPtr SchedContext -> [Refill] -> Kernel ()
> setRefills scPtr refills = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefills = refills })

> refillAddTail :: PPtr SchedContext -> Refill -> Kernel ()
> refillAddTail scPtr rfl = do
>    sc <- getSchedContext scPtr
>    refills <- return $ scRefills sc
>    assert (length refills < scRefillMax sc) "Length of Refill list must be less than the maximum"
>    setSchedContext scPtr (sc { scRefills = refills ++ [rfl] })

> maybeAddEmptyTail :: PPtr SchedContext -> Kernel ()
> maybeAddEmptyTail scPtr = do
>     robin <- isRoundRobin scPtr
>     when robin $ do
>         curTime <- getCurTime
>         refillAddTail scPtr (Refill { rTime = curTime, rAmount = 0 })

> refillNew :: PPtr SchedContext -> Int -> Ticks -> Ticks -> Kernel ()
> refillNew scPtr maxRefills budget period = do
>     assert (minBudget < budget) "Budget must be greater than the minimum"
>     curTime <- getCurTime
>     refill <- return $ Refill { rTime = curTime, rAmount = budget }
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr $ sc { scPeriod = period,
>                                  scRefills = [refill],
>                                  scRefillMax = maxRefills }
>     maybeAddEmptyTail scPtr

> scheduleUsed :: [Refill] -> Refill -> [Refill]
> scheduleUsed [] new = [new]
> scheduleUsed (x:rs) new =
>     let rtl = last (x:rs) in
>     if (rAmount new < minBudget) && (length rs /= 0) then
>         let newtl = rtl { rAmount = rAmount rtl + rAmount new,
>                           rTime = max (rTime new) (rTime rtl) } in
>         (init (x:rs)) ++ [newtl]
>     else if rTime new <= rTime rtl then
>         let newtl = rtl { rAmount = rAmount rtl + rAmount new } in
>         (init (x:rs)) ++ [newtl]
>     else (x:rs) ++ [new]

> mergeRefill :: Refill -> Refill -> Refill
> mergeRefill r1 r2 =
>     Refill { rTime = rTime r1, rAmount = rAmount r2 + rAmount r1 }

> canMergeRefill r1 r2 = rTime r2 <= rTime r1 + rAmount r1

> refillsMergePrefix :: [Refill] -> [Refill]
> refillsMergePrefix [] = []
> refillsMergePrefix [r] = [r]
> refillsMergePrefix (r1:r2:rs) =
>     if canMergeRefill r1 r2
>         then refillsMergePrefix ((mergeRefill r1 r2) : rs)
>         else r1:r2:rs

> refillUnblockCheck :: PPtr SchedContext -> Kernel ()
> refillUnblockCheck scPtr = do
>     robin <- isRoundRobin scPtr
>     when (not robin) $ do
>         ct <- getCurTime
>         setReprogramTimer True
>         refills <- getRefills scPtr
>         refills' <- return $ refillsMergePrefix ((head refills) { rTime = ct } : tail refills)
>         setRefills scPtr refills'

> minBudgetMerge :: Bool -> [Refill] -> [Refill]
> minBudgetMerge _ [] = []
> minBudgetMerge _ [r] = [r]
> minBudgetMerge full (r0:r1:rs) =
>     if rAmount r0 < minBudget || full
>     then minBudgetMerge False (r1 { rAmount = rAmount r1 + rAmount r0 } : rs)
>     else r0:r1:rs

> refillsBudgetCheck :: Ticks -> Ticks -> [Refill] -> (Ticks, [Refill])
> refillsBudgetCheck period usage [] = (usage, [])
> refillsBudgetCheck period usage (r:rs) =
>     if rAmount r <= usage && 0 < rAmount r
>     then refillsBudgetCheck period (usage - rAmount r)
>              (scheduleUsed rs (r { rTime = rTime r + period }))
>     else (usage, r:rs)

> refillBudgetCheck :: PPtr SchedContext -> Ticks -> Ticks -> Kernel ()
> refillBudgetCheck scPtr usage capacity = do
>     sc <- getSchedContext scPtr
>     full <- refillFull scPtr
>     assert (capacity < minBudget || full) "refillBudgetCheck: this function should only be called when the sc is out of budget"
>     period <- return $ scPeriod sc
>     assert (period > 0) "refillBudgetCheck: period must be greater than 0"
>     refills <- return $ scRefills sc
>     (usage', refills') <- return (if capacity == 0 then
>         refillsBudgetCheck period usage refills
>         else (usage, refills))
>     refills'' <- return (if capacity == 0 && 0 < usage' then
>         (let r1 = head refills';
>              r1' = r1 { rTime = rTime r1 + usage };
>              rs = tail refills'
>          in if length rs /= 0 && canMergeRefill r1' (head rs)
>             then (mergeRefill r1' (head rs)) : tail rs
>             else r1' : rs)
>         else refills')
>     setRefills scPtr refills''
>     capacity <- refillCapacity scPtr usage'
>     ready <- refillReady scPtr
>     when (capacity > 0 && ready) $ refillSplitCheck scPtr usage'
>     full <- refillFull scPtr
>     refills''' <- getRefills scPtr
>     setRefills scPtr (minBudgetMerge full refills''')

> refillSplitCheck :: PPtr SchedContext -> Time -> Kernel ()
> refillSplitCheck scPtr usage = do
>    ct <- getCurTime
>    sc <- getSchedContext scPtr
>    refills <- return $ scRefills sc
>    rfhd <- return $ refillHd sc
>    assert (0 < usage && usage <= rAmount rfhd) "Time usage must be within (0, rAmount of the refills head]"
>    assert (rTime rfhd <= ct) "rTime must not be greater than the current time"

>    remaining <- return $ rAmount rfhd - usage
>    new <- return (Refill { rTime = rTime rfhd + scPeriod sc, rAmount = usage })

>    if length refills == scRefillMax sc || remaining < minBudget
>        then if length refills == 1
>                 then setRefills scPtr [new { rAmount = rAmount new + remaining }]
>                 else
>                     let r2 = head (tail refills);
>                         rs = tail (tail refills)
>                     in setRefills scPtr
>                            (scheduleUsed (r2 { rAmount = rAmount r2 + remaining } : rs) new)
>             else
>                 setRefills scPtr
>                     (scheduleUsed (rfhd { rAmount = remaining, rTime = rTime rfhd + usage } : tail refills) new)

> refillUpdate :: PPtr SchedContext -> Ticks -> Ticks -> Int -> Kernel ()
> refillUpdate scPtr newPeriod newBudget newMaxRefills = do
>    sc <- getSchedContext scPtr
>    refillHd <- return $ refillHd sc
>    curTime <- getCurTime
>    ready <- refillReady scPtr
>    newTime <- return $ if ready then curTime else rTime refillHd
>    if (rAmount refillHd >= newBudget)
>        then do
>            setSchedContext scPtr (sc { scPeriod = newPeriod,
>                                        scRefillMax = newMaxRefills,
>                                        scRefills = [Refill newTime newBudget] })
>            maybeAddEmptyTail scPtr
>        else
>            setSchedContext scPtr (sc { scPeriod = newPeriod,
>                                        scRefillMax = newMaxRefills,
>                                        scRefills = [Refill newTime (rAmount refillHd),
>                                                     Refill (newTime + newPeriod)
>                                                            (newBudget - rAmount refillHd)] })

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
>     assert (tptrOpt /= Nothing) "schedContextResume: scPtr must have an associated TCB"
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
>     assert (tptrOpt /= Nothing) "schedContextUnbindTCB: option of TCB pointer must not be Nothing"
>     let tptr = fromJust tptrOpt
>     cur <- getCurThread
>     when (tptr == cur) $ rescheduleRequired
>     tcbSchedDequeue tptr
>     tcbReleaseRemove tptr
>     threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tptr
>     setSchedContext scPtr $ sc { scTCB = Nothing }


> schedContextDonate :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextDonate scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     fromOpt <- return $ scTCB sc
>     when (fromOpt /= Nothing) $ do
>         from <- return $ fromJust fromOpt
>         tcbSchedDequeue from
>         threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) from
>         cur <- getCurThread
>         action <- getSchedulerAction
>         flag <- return (case action of
>                           SwitchToThread candidate -> from == candidate
>                           _ -> False)
>         when (from == cur || flag) rescheduleRequired
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
>     if (consumed >= max_ticks_to_us)
>         then do
>             setSchedContext scPtr $ sc { scConsumed = scConsumed sc - max_ticks_to_us }
>             return max_ticks_to_us
>         else do
>             setSchedContext scPtr $ sc { scConsumed = 0 }
>             return $ ticks_to_us consumed

> schedContextYieldTo :: PPtr SchedContext -> [Word] -> Kernel ()
> schedContextYieldTo scPtr buffer = do
>     sc <- getSchedContext scPtr
>     scYfOpt <- return $ scYieldFrom sc
>     when (scYfOpt /= Nothing) $
>         schedContextCompleteYieldTo $ fromJust scYfOpt
>     flag <- return True
>     refillUnblockCheck scPtr
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTCB sc
>     schedulable <- isSchedulable tptr False
>     when schedulable $ do
>         sufficient <- refillSufficient scPtr 0
>         ready <- refillReady scPtr
>         assert (sufficient && ready) "schedContextYieldTo: refill must be sufficient and ready"
>         ctPtr <- getCurThread
>         prios <- threadGet tcbPriority tptr
>         ctPrios <- threadGet tcbPriority ctPtr
>         if (prios < ctPrios)
>             then do
>                 tcbSchedDequeue tptr
>                 tcbSchedEnqueue tptr
>             else do
>                 flag <- return False
>                 setSchedContext scPtr (sc { scYieldFrom = Just ctPtr })
>                 threadSet (\tcb -> tcb { tcbYieldTo = Just scPtr }) ctPtr
>                 possibleSwitchTo tptr
>     when flag $ setConsumed scPtr (PPtr (head buffer))

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
>         schedContextUnbindReply scPtr
>     InvokeSchedContextYieldTo scPtr buffer -> do
>         schedContextYieldTo scPtr buffer

> invokeSchedControlConfigure :: SchedControlInvocation -> KernelF SyscallError ()
> invokeSchedControlConfigure iv = case iv of
>     InvokeSchedControlConfigure scPtr budget period mRefills badge -> withoutFailure $ do
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr $ sc { scBadge = badge }
>         let (period, mRefills) = if budget == period then (0, minRefills) else (period, mRefills)
>         when (scTCB sc /= Nothing) $ do
>             tptr <- return $ fromJust $ scTCB sc
>             tcbReleaseRemove tptr
>             tcbSchedDequeue tptr
>             curSc <- getCurSc
>             when (curSc == scPtr) $ do
>                 result <- checkBudget
>                 when result $ commitTime
>             if 0 < scRefillMax sc
>                 then do
>                     runnable <- isRunnable tptr
>                     when runnable $ refillUpdate scPtr period budget mRefills
>                     schedContextResume scPtr
>                     ctPtr <- getCurThread
>                     if (tptr == ctPtr)
>                         then rescheduleRequired
>                         else when runnable $ possibleSwitchTo tptr
>                 else refillNew scPtr mRefills budget period

> isCurDomainExpired :: Kernel Bool
> isCurDomainExpired = do
>     domainTime <- getDomainTime
>     consumedTime <- getConsumedTime
>     return $ domainTime < consumedTime + minBudget

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
>                 newHd <- return $ (refillHd sc) { rTime = rTime (refillHd sc) - consumed }
>                 newTl <- return $ (refillTl sc) { rTime = rTime (refillTl sc) + consumed }
>                 setRefills scPtr (newHd : [newTl])
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
>         Just ntfnPtr -> do
>             ntfn <- getNotification ntfnPtr
>             setNotification ntfnPtr (ntfn { ntfnSc = Nothing })
>             setSchedContext scPtr (sc { scNtfn = Nothing })

> schedContextUnbindReply :: PPtr SchedContext -> Kernel ()
> schedContextUnbindReply scPtr = do
>     sc <- getSchedContext scPtr
>     mapM_ (setReplySc Nothing) (scReplies sc)
>     setSchedContext scPtr (sc { scReplies = [] })

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
> refillAbsoluteMax (SchedContextCap _ sc) =
>     ((1 `shiftL` sc) - coreSchedContextBytes) `div` refillSizeBytes + minRefills
> refillAbsoluteMax _ = 0

> schedContextCancelYieldTo :: PPtr TCB -> Kernel ()
> schedContextCancelYieldTo tptr = do
>     scPtrOpt <- threadGet tcbYieldTo tptr
>     when (scPtrOpt /= Nothing) $ do
>         scPtr <- return $ fromJust scPtrOpt
>         sc <- getSchedContext scPtr
>         threadSet (\tcb -> tcb { tcbYieldTo = Nothing }) tptr
>         setSchedContext scPtr (sc { scYieldFrom = Nothing })

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

