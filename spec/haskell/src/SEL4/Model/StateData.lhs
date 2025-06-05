%
% Copyright 2022, Proofcraft Pty Ltd
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the high-level structures used to represent the
state of the entire system, and the types and functions used to
perform basic operations on the state.

\begin{impdetails}

We use the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Model.StateData (
>         module SEL4.Model.StateData,
>         module Control.Monad, get, gets, put, modify, asks
>     ) where

The architecture-specific definitions are imported qualified with the "Arch" prefix.

> import Prelude hiding (Word)
> import qualified SEL4.Model.StateData.TARGET as Arch

\begin{impdetails}

> import SEL4.Config (numDomains)
> import SEL4.API.Types
> import {-# SOURCE #-} SEL4.Model.PSpace
> import SEL4.Object.Structures
> import SEL4.Machine
> import SEL4.Machine.Hardware.TARGET (VMPageSize)

> import Data.Array
> import qualified Data.Set
> import Data.Helpers
> import Data.WordLib
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Reader
> import Data.Word(Word64)

\end{impdetails}

\subsection{Types}

\subsubsection{Kernel State}

The top-level kernel state structure is called "KernelState". It contains:

> data KernelState = KState {

\begin{itemize}
\item the physical address space, of type "PSpace" (defined in \autoref{sec:model.pspace});

>         ksPSpace :: PSpace,

\item ghost state, i.e. meta-information about the kernel objects living in "PSpace";

>         gsUserPages :: Word -> (Maybe VMPageSize),
>         gsCNodes :: Word -> (Maybe Int),
>         gsUntypedZeroRanges :: Data.Set.Set (Word, Word),

\item the cyclic domain schedule;

>         ksDomScheduleIdx :: Int,
>         ksDomSchedule :: [DomainSchedule],

\item the active security domain and the number to ticks remaining before it changes;

>         ksCurDomain :: Domain,
>         ksDomainTime :: Word64,

\item an array of ready queues, indexed by thread priority and domain (see "getQueue");

>         ksReadyQueues :: Array (Domain, Priority) ReadyQueue,

>         ksReleaseQueue :: ReleaseQueue,

\item a bitmap for each domain; each bit represents the presence of a runnable thread for a specific priority

>         ksReadyQueuesL1Bitmap :: Array (Domain) Word,
>         ksReadyQueuesL2Bitmap :: Array (Domain, Int) Word,

\item a pointer to the current thread's control block;

>         ksCurThread :: PPtr TCB,

\item a pointer to the idle thread's control block;

>         ksIdleThread :: PPtr TCB,

\item a pointer to the idle thread's scheduling context;

>         ksIdleSC :: PPtr SchedContext,

>         ksConsumedTime :: Time,

>         ksCurTime :: Time,

>         ksCurSc :: PPtr SchedContext,

>         ksReprogramTimer :: Bool,

\item the required action of the scheduler next time it runs;

>         ksSchedulerAction :: SchedulerAction,

\item the interrupt controller's state data;

>         ksInterruptState :: InterruptState,

\item the number of preemption point runs where IRQs have not been checked

>         ksWorkUnitsCompleted :: Word,

\item and some architecture-defined state data.

>         ksArchState :: Arch.KernelState }

\end{itemize}

Note that this definition of "KernelState" assumes a single processor. The behaviour of the kernel on multi-processor systems is not specified by this document.

Note that the priority bitmap is split up into two levels. In order to check to see whether a priority has a runnable thread on a 32-bit system with a maximum priority of 255, we use the high 3 bits of the priority as an index into the level 1 bitmap. If the bit at that index is set, we use those same three bits to obtain a word from the level 2 bitmap. We then use the remaining 5 bits to index into that word. If the bit is set, the queue for that priority is non-empty.

Note also that due the common case being scheduling high-priority threads, the level 2 bitmap array is reversed to improve cache locality.

\subsubsection{Monads}

Kernel functions are sequences of operations that transform a "KernelState" object. They are encapsulated in the monad "Kernel", which uses "StateT" to add a "KernelState" data structure to the monad that encapsulates the simulated machine, "MachineMonad". This allows functions to read and modify the kernel state.

> type Kernel = StateT KernelState MachineMonad

Note that there is no error-signalling mechanism available to functions in "Kernel". Therefore, all errors encountered in such functions are fatal, and will halt the kernel. See \autoref{sec:model.failures} for the definition of monads used for error handling.

Read-only, potentially failing functions:

> type ReaderM s = ReaderT s Maybe
> type KernelR = ReaderM KernelState

To run a "ReaderM" inside a state monad stack, e.g. the "Kernel" monad, use "getsJust":

> getsJust :: MonadFail m => ReaderM s a -> StateT s m a
> getsJust r = do
>     x <- gets (runReaderT r)
>     maybe (fail "must return something") return x

\subsubsection{Scheduler Queues}

The ready queue is simply a list of threads that are ready to
run. Each thread in this list is at the same priority level.

> type ReadyQueue = TcbQueue

> type ReleaseQueue = TcbQueue

\subsection{Kernel State Functions}

The following two functions are used to get and set the value of the
current thread pointer which is stored in the kernel state.

\begin{impdetails}

These functions have the same basic form as many
others in the kernel which fetch or set the value of some part of the
state data. They make use of "gets" and "modify", two functions which
each apply a given function to the current state --- either returning
some value extracted from the state, or calculating a new state which
replaces the previous one.

\end{impdetails}

> getCurThread :: Kernel (PPtr TCB)
> getCurThread = gets ksCurThread

> setCurThread :: PPtr TCB -> Kernel ()
> setCurThread tptr = do
>   stateAssert idleThreadNotQueued "The idle thread cannot be in the ready queues"
>   modify (\ks -> ks { ksCurThread = tptr })

In many places, we would like to be able to use the fact that threads in the
ready queues have runnable' thread state. We add an assertion that it does hold.

> ready_qs_runnable :: KernelState -> Bool
> ready_qs_runnable _ = True

Similarly, these functions access the idle thread pointer, the idle sc pointer, the ready queue for a given priority level (adjusted to account for the active security domain), the requested action of the scheduler, and the interrupt handler state.

> getIdleThread :: Kernel (PPtr TCB)
> getIdleThread = gets ksIdleThread

> getIdleSC :: Kernel (PPtr SchedContext)
> getIdleSC = gets ksIdleSC

> setIdleThread :: PPtr TCB -> Kernel ()
> setIdleThread tptr = modify (\ks -> ks { ksIdleThread = tptr })

> getQueue :: Domain -> Priority -> Kernel ReadyQueue
> getQueue qdom prio = gets (\ks -> ksReadyQueues ks ! (qdom, prio))

> setQueue :: Domain -> Priority -> ReadyQueue -> Kernel ()
> setQueue qdom prio q = modify (\ks -> ks { ksReadyQueues = (ksReadyQueues ks)//[((qdom, prio),q)] })

> getReleaseQueue :: Kernel ReleaseQueue
> getReleaseQueue = gets ksReleaseQueue

> readReleaseQueue :: KernelR ReleaseQueue
> readReleaseQueue = asks ksReleaseQueue

> setReleaseQueue :: ReleaseQueue -> Kernel ()
> setReleaseQueue releaseQueue = modify (\ks -> ks { ksReleaseQueue = releaseQueue })

> getConsumedTime :: Kernel Time
> getConsumedTime = gets ksConsumedTime

> setConsumedTime :: Time -> Kernel ()
> setConsumedTime consumedTime = modify (\ks -> ks { ksConsumedTime = consumedTime })

> getCurSc :: Kernel (PPtr SchedContext)
> getCurSc = gets ksCurSc

> readCurSc :: KernelR (PPtr SchedContext)
> readCurSc = asks ksCurSc

> setCurSc :: PPtr SchedContext -> Kernel ()
> setCurSc scptr = modify (\ks -> ks { ksCurSc = scptr })

> getSchedulerAction :: Kernel SchedulerAction
> getSchedulerAction = gets ksSchedulerAction

> setSchedulerAction :: SchedulerAction -> Kernel ()
> setSchedulerAction a = modify (\ks -> ks { ksSchedulerAction = a })

> getInterruptState :: Kernel InterruptState
> getInterruptState = gets ksInterruptState

> setInterruptState :: InterruptState -> Kernel ()
> setInterruptState a = modify (\ks -> ks { ksInterruptState = a })

> getWorkUnits :: Kernel Word
> getWorkUnits = gets ksWorkUnitsCompleted

> setWorkUnits :: Word -> Kernel ()
> setWorkUnits a = modify (\ks -> ks { ksWorkUnitsCompleted = a })

> modifyWorkUnits :: (Word -> Word) -> Kernel ()
> modifyWorkUnits f = modify (\ks -> ks { ksWorkUnitsCompleted =
>                                         f (ksWorkUnitsCompleted ks) })

TODO use this where update is restricted to arch state instead of fiddling in place

> modifyArchState :: (Arch.KernelState -> Arch.KernelState) -> Kernel ()
> modifyArchState f = modify (\s -> s { ksArchState = f (ksArchState s) })

These functions access and modify the current domain and the number of ticks remaining until the current domain changes.

> curDomain :: Kernel Domain
> curDomain = gets ksCurDomain

> usInMs :: Word64
> usInMs = 1000

> nextDomain :: Kernel ()
> nextDomain = modify (\ks ->
>   let ksDomScheduleIdx' = (ksDomScheduleIdx ks + 1) `mod` length (ksDomSchedule ks) in
>   let next = ksDomSchedule ks !! ksDomScheduleIdx'
>   in ks { ksWorkUnitsCompleted = 0,
>           ksDomScheduleIdx = ksDomScheduleIdx',
>           ksCurDomain = dschDomain next,
>           ksDomainTime = usToTicks ((dschLength next) * usInMs),
>           ksReprogramTimer = True })

> getDomainTime :: Kernel Word64
> getDomainTime = gets ksDomainTime

> setDomainTime :: Ticks -> Kernel ()
> setDomainTime domainTime = modify (\ks -> ks { ksDomainTime = domainTime })

> getCurTime :: Kernel Time
> getCurTime = gets ksCurTime

> readCurTime :: KernelR Time
> readCurTime = asks ksCurTime

> setCurTime :: Time -> Kernel ()
> setCurTime curTime = modify (\ks -> ks { ksCurTime = curTime })

> getReprogramTimer :: Kernel Bool
> getReprogramTimer = gets ksReprogramTimer

> setReprogramTimer :: Bool -> Kernel ()
> setReprogramTimer reprogramTimer = modify (\ks -> ks { ksReprogramTimer = reprogramTimer })

> decDomainTime :: Kernel ()
> decDomainTime = modify (\ks -> ks { ksDomainTime = ksDomainTime ks - 1 })

\subsection{Initial Kernel State}

A new kernel state structure contains an empty physical address space, a set of empty scheduler queues, and undefined values for the other global variables, which must be set during the bootstrap sequence.

> newKernelState :: PAddr -> (KernelState, [PAddr])
> newKernelState data_start = (state', frames) where
>     state' = KState {
>         ksPSpace = newPSpace,
>         gsUserPages = (\_ -> Nothing),
>         gsCNodes = (\_ -> Nothing),
>         gsUntypedZeroRanges = Data.Set.empty,
>         ksDomScheduleIdx = 0,
>         ksDomSchedule = [(0, 15), (2, 42), (1, 73)],
>         ksCurDomain = 0,
>         ksDomainTime = 15,
>         ksReadyQueues =
>             funPartialArray (const (TcbQueue {tcbQueueHead = Nothing, tcbQueueEnd = Nothing}))
>                             ((0, 0), (fromIntegral numDomains, maxPriority)),
>         ksReadyQueuesL1Bitmap = funPartialArray (const 0) (0, fromIntegral numDomains),
>         ksReadyQueuesL2Bitmap =
>             funPartialArray (const 0)
>                 ((0, 0), (fromIntegral numDomains, l2BitmapSize)),
>         ksReleaseQueue = TcbQueue {tcbQueueHead = Nothing, tcbQueueEnd = Nothing},
>         ksCurThread = error "No initial thread",
>         ksIdleThread = error "Idle thread has not been created",
>         ksIdleSC = error "Idle scheduling context has not been created",
>         ksReprogramTimer = False,
>         ksConsumedTime = 0,
>         ksCurTime = 0,
>         ksCurSc = error "No initial scheduling context",
>         ksSchedulerAction = error "scheduler action has not been set",
>         ksInterruptState = error "Interrupt controller is uninitialised",
>         ksWorkUnitsCompleted = 0,
>         ksArchState = archState }
>     (archState, frames) = Arch.newKernelState data_start

\subsection{Performing Machine Operations}

The following function allows the machine monad to be directly accessed from kernel code.

> doMachineOp :: MachineMonad a -> Kernel a
> doMachineOp = lift

\subsection{Miscellaneous Monad Functions}

The functions "ifM", and "whenM" are monadic versions of "if", and "when", where the condition runs in the monad.

> ifM :: Monad m => m Bool -> m a -> m a -> m a
> ifM test t f = do
>     check <- test
>     if check then t else f

> whenM :: Monad m => m Bool -> m () -> m ()
> whenM test body = ifM test body (return ())

The function "whileM" allows writing while loops where the loop body and the condition are monads. The body is run until the test returns False.

> whileM :: Monad m => m Bool -> m () -> m ()
> whileM test body = whenM test $ body >> whileM test body

The function "whileLoop" emulates the definition whileLoop from NonDetMonad.thy in lib.

> condition :: MonadState s m => (s -> Bool) -> m a -> m a -> m a
> condition cond left right = get >>= \s -> if cond s then left else right

> whileLoop :: MonadState s m => (a -> s -> Bool) -> (a -> m a) -> a -> m a
> whileLoop cond body r = condition (cond r) (body r) (return r) >>= whileLoop cond body

The functions "orM" and "andM" allow composing conditions that run in a monad. These are "short-circuiting", in that if a monad doesn't need to be evaluated to return a result, it won't be.

> orM :: Monad m => m Bool -> m Bool -> m Bool
> orM a b = ifM a (return True) b

> andM :: Monad m => m Bool -> m Bool -> m Bool
> andM a b = ifM a b (return False)

\subsubsection{Assertions and Undefined Behaviour}

The function "assert" is used to state that a predicate must be true at a given point. If it is not, the behaviour of the kernel is undefined. The Haskell model will not terminate in this case.

> assert :: MonadFail m => Bool -> String -> m ()
> assert p e = if p then return () else fail $ "Assertion failed: " ++ e

The function "stateAssert" is similar to "assert", except that it reads the current state. This is typically used for more complex assertions that cannot be easily expressed in Haskell; in this case, the asserted function is "const True" in Haskell but is replaced with something stronger in the Isabelle translation.

> stateAssert :: MonadFail m => MonadState s m => (s -> Bool) -> String -> m ()
> stateAssert f e = get >>= \s -> assert (f s) e

A version of "stateAssert" that can be used within functions that are in the reader monad

> readStateAssert :: MonadFail m => MonadReader s m => (s -> Bool) -> String -> m ()
> readStateAssert f e = ask >>= \s -> assert (f s) e

The "capHasProperty" function is used with "stateAssert". As explained above, it is "const True" here, but is strengthened to actually check the capability in the translation to Isabelle.

> capHasProperty :: PPtr CTE -> (Capability -> Bool) -> KernelState -> Bool
> capHasProperty _ _ = const True

\subsubsection{Searching a List}

The function "findM" searches a list, returning the first item for which the given function returns "True". It is the monadic equivalent of "Data.List.find".

> findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
> findM _ [] = return Nothing
> findM f (x:xs) = do
>     r <- f x
>     if r then return $ Just x else findM f xs

In many places, we would like to be able to use the fact that `sym_refs (state_refs_of' s)`
holds. We add an assertion that it does hold. We may prove this assertion is true
using the rule `state_refs_of_cross_eq`.

> sym_refs_asrt :: KernelState -> Bool
> sym_refs_asrt _ = True

We would also like to use the fact that `valid_replies'` holds for replies linked to an SC. We
does this by adding an assertion and proving it True by using .

> valid_replies'_sc_asrt :: PPtr Reply -> KernelState -> Bool
> valid_replies'_sc_asrt _ _ = True

To ease the burden of proof for weakest precondition rules involving ThreadControlSched tcb
invocations, we assert various conditions that hold in the abstract.

> tcs_cross_asrt1 :: PPtr TCB -> Maybe (Maybe (PPtr SchedContext)) -> KernelState -> Bool
> tcs_cross_asrt1 _ _ _ = True

> tcs_cross_asrt2 :: KernelState -> Bool
> tcs_cross_asrt2 _ = True

A few places in the proofs would like to know that ct_not_inQ holds. We add an assertion that it
does hold. We may prove that this assertion is true using ct_not_inQ_cross.

> ct_not_inQ_asrt :: KernelState -> Bool
> ct_not_inQ_asrt _ = True

An assert that will say that `sch_act_wf (ksSchedulerAction s) s` holds. We may prove this assertion
is true using the rule sch_act_wf_cross.

> sch_act_wf_asrt :: KernelState -> Bool
> sch_act_wf_asrt _ = True

An assert that will say that `valid_idle' s` holds. We may prove this assertion
is true using the rule valid_idle'_cross.

> valid_idle'_asrt :: KernelState -> Bool
> valid_idle'_asrt _ = True

An assert that will say that `cur_tcb' s` holds. We may prove this assertion
is true using the rule cur_tcb'_cross.

> cur_tcb'_asrt :: KernelState -> Bool
> cur_tcb'_asrt _ = True

Asserts used for first phase, non-blocking, non-calling handle_invocation.
Each stating that `sch_act_sane`, `!pd. ksCurThread s notin set (ksReadyQueues s pd)`,
and `ct_active' s` holds.

> sch_act_sane_asrt :: KernelState -> Bool
> sch_act_sane_asrt _ = True

> ct_not_ksQ_asrt :: KernelState -> Bool
> ct_not_ksQ_asrt _ = True

> ct_active'_asrt :: KernelState -> Bool
> ct_active'_asrt _ = True

Assert stating that, when scheduler action is resume, the current thread is activatable.
Used in callKernel.

> rct_imp_activatable'_asrt :: KernelState -> Bool
> rct_imp_activatable'_asrt _ = True

Various lemmas in Refine_C.thy would like the fact that the current thread is
activatable' after schedule runs. We add an assertion that this is the case.

> ct_activatable'_asrt :: KernelState -> Bool
> ct_activatable'_asrt _ = True

An assert that will say that the return value of findTimeAfter
is a pointer in the release queue.

> findTimeAfter_asrt :: PPtr TCB -> KernelState -> Bool
> findTimeAfter_asrt _ _ = True

An assert that will say that `ready_or_release'` holds. That is, no thread
has both the tcbQueued and tcbInReleaseQueue flag set.

> ready_or_release'_asrt :: KernelState -> Bool
> ready_or_release'_asrt _ = True

An assert that will say that the tcbInReleaseQueue flag is not set.

> not_tcbInReleaseQueue_asrt :: PPtr TCB -> KernelState -> Bool
> not_tcbInReleaseQueue_asrt _ _ = True

An assert that will say that every thread in the release queue is associated
with an active scheduling context.

> tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt :: KernelState -> Bool
> tcbInReleaseQueue_imp_active_sc_tcb_at'_asrt _ = True

An assert that will say that if the release queue is not empty, then the head
of the release queue is associated with an active scheduling context.

> tcbQueueHead_ksReleaseQueue_active_sc_tcb_at'_asrt :: KernelState -> Bool
> tcbQueueHead_ksReleaseQueue_active_sc_tcb_at'_asrt _ = True

An assert that will say that the tcbQueued flag of the thread is not set.

> not_tcbQueued_asrt :: PPtr TCB -> KernelState -> Bool
> not_tcbQueued_asrt _ _ = True

Several asserts about ksReadyQueues

> ksReadyQueues_asrt :: KernelState -> Bool
> ksReadyQueues_asrt _ = True

Several asserts about ksReleaseQueue

> ksReleaseQueue_asrt :: KernelState -> Bool
> ksReleaseQueue_asrt _ = True

An assert that will say that the idle thread is not in a ready queue

> idleThreadNotQueued :: KernelState -> Bool
> idleThreadNotQueued _ = True

An assert that will say that there is a TCB at the given pointer

> tcb_at'_asrt :: PPtr TCB -> KernelState -> Bool
> tcb_at'_asrt _ _ = True

An assert that will say that there is a scheduling context at the given pointer

> sc_at'_asrt :: PPtr SchedContext -> KernelState -> Bool
> sc_at'_asrt _ _ = True

An assert that will say that there is an active scheduling context at the given pointer

> active_sc_at'_asrt :: PPtr SchedContext -> KernelState -> Bool
> active_sc_at'_asrt _ _ = True

An assert that will say that there is a TCB with active' thread state at the given pointer

> active_tcb_at'_asrt :: PPtr TCB -> KernelState -> Bool
> active_tcb_at'_asrt _ _ = True

An assert that will say that the current thread is associated with an active scheduling context

> active_sc_tcb_at'_ct_asrt :: KernelState -> Bool
> active_sc_tcb_at'_ct_asrt _ = True

An assert that will say that the current thread is not in the release queue

> ct_not_in_release_q'_asrt :: KernelState -> Bool
> ct_not_in_release_q'_asrt _ = True

An assert that will say that valid_tcbs' holds

> valid_tcbs'_asrt :: KernelState -> Bool
> valid_tcbs'_asrt _ = True

An assert that will say that valid_objs' holds

> valid_objs'_asrt :: KernelState -> Bool
> valid_objs'_asrt _ = True

An assert that will say that invs' holds

> invs'_asrt :: KernelState -> Bool
> invs'_asrt _ = True

An assert that will say that weak_sch_act_wf holds

> weak_sch_act_wf_asrt :: KernelState -> Bool
> weak_sch_act_wf_asrt _ = True

An assert that will say that sch_act_simple holds

> sch_act_simple_asrt :: KernelState -> Bool
> sch_act_simple_asrt _ = True

An assert that will say that priority_ordered' holds of the given list

> priority_ordered'_asrt :: [PPtr TCB] -> KernelState -> Bool
> priority_ordered'_asrt _ _ = True

An assert that will say that valid_domain_list' holds

> valid_domain_list'_asrt :: KernelState -> Bool
> valid_domain_list'_asrt _ = True
