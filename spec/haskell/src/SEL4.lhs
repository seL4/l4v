%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This is the top-level module; it defines the interface between the kernel and the user-level simulator.

> module SEL4 (
>     module SEL4.Machine,
>     Event(..), Syscall(..), callKernel, asUser,
>     Kernel, KernelState, getCurThread,
>     lookupCap,
>     module SEL4.API.Types,
>     module SEL4.Kernel.Init,
>     module SEL4.Object.Structures,
>     ) where

> import SEL4.API
> import SEL4.Machine
> import SEL4.Kernel.Init
> import SEL4.API.Types
> import SEL4.Kernel.CSpace(lookupCap)
> import SEL4.Kernel.Thread(schedule, activateThread)
> import SEL4.Model.StateData(KernelState, Kernel, getCurThread, doMachineOp, stateAssert, rct_imp_activatable'_asrt, cur_tcb'_asrt)
> import SEL4.Model.Preemption(withoutPreemption)
> import SEL4.Object.Structures
> import SEL4.Object.TCB(asUser, mcsPreemptionPoint)
> import SEL4.Object.Interrupt(maybeHandleInterrupt)
> import Control.Monad.Except
> import Data.Maybe

\subsection{Kernel Entry Point}

The following function is called by the simulator whenever an event
occurs which the kernel must handle. Such events include interrupts,
faults, and system calls; the set of possible events is defined in
\autoref{sec:api.types}.

> callKernel :: Event -> Kernel ()
> callKernel ev = do
>     stateAssert fastpathKernelAssertions ""
>     stateAssert cur_tcb'_asrt "`cur_tcb'`"
>     runExceptT $ handleEvent ev
>         `catchError` (\_ -> withoutPreemption $ do
>                       mcsPreemptionPoint irq_opt
>                       maybeHandleInterrupt True)
>     stateAssert rct_imp_activatable'_asrt
>         "if the scheduler action is `ResumeCurrentThread`, then the current thread is `activatable'`"
>     schedule
>     stateAssert rct_imp_activatable'_asrt
>         "if the scheduler action is `ResumeCurrentThread`, then the current thread is `activatable'`"
>     activateThread
>     stateAssert kernelExitAssertions ""

This will be replaced by actual assertions in the proofs:

> kernelExitAssertions :: KernelState -> Bool
> kernelExitAssertions _ = True

During refinement proofs, abstract invariants are used to show properties on the
design spec without corresponding invariants on the concrete level. Since the
fast path proofs do not have access to the abstract invariant level nor the
state relation, any extra properties need to be crossed over via this assertion.
This will be replaced by actual assertions in the proofs.

> fastpathKernelAssertions :: KernelState -> Bool
> fastpathKernelAssertions _ = True
