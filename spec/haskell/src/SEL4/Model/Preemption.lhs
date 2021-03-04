%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the types and functions used by the kernel model to implement preemption points and non-preemptible sections in the kernel code.

> module SEL4.Model.Preemption(
>     KernelP, withoutPreemption
>     ) where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Model.StateData

> import Control.Monad.Except

\end{impdetails}

\subsection{Types}

\subsubsection{Interrupts}

Objects of this type are thrown from an "ExceptT" monad transformer when the simulator signals a pending interrupt at a kernel preemption point. The nature of the interrupt is not relevant here, because the simulator will send it to the kernel model as an "Event" once the kernel has been preempted.

\subsubsection{Monads}

The "KernelP" monad is a transformation of the "Kernel" monad used for functions which may be preempted. Any function in this monad must not leave the kernel in an inconsistent state when calling other functions in the monad (though the model has no means of effectively enforcing this restriction).

> type KernelP a = ExceptT () Kernel a

\subsection{Functions}

If an operation must be performed during which the kernel state is temporarily inconsistent, it should be performed in the argument of a "withoutPreemption" call, to ensure that no preemption points are encountered during the operation.

> withoutPreemption :: Kernel a -> KernelP a
> withoutPreemption = lift

For MCS, the function preemptionPoint is defined at the end of Object/SchedContext.lhs due to its dependencies on some functions on scheduling contexts.
