%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the structures which represent kernel objects in the modelled physical memory.

\begin{impdetails}

% Uses hand-crafted .lhs-boot file

This module uses the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.Structures (
>         module SEL4.Object.Structures,
>         module SEL4.Object.Structures.TARGET
>     ) where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Config (numPriorities, numDomains)
> import SEL4.Machine
> import SEL4.API.Types
> import SEL4.API.Types.Universal
> import SEL4.API.Types.TARGET
> import SEL4.API.Failures

> import SEL4.Object.Structures.TARGET

> import Data.Array
> import Data.Bits
> import Data.WordLib

\end{impdetails}

\subsection{Capabilities}

This is the type used to represent a capability.

> data Capability
>         = ThreadCap {
>             capTCBPtr :: PPtr TCB }
>         | NullCap
>         | NotificationCap {
>             capNtfnPtr :: PPtr Notification,
>             capNtfnBadge :: Word,
>             capNtfnCanSend, capNtfnCanReceive :: Bool }
>         | IRQHandlerCap {
>             capIRQ :: IRQ }
>         | EndpointCap {
>             capEPPtr :: PPtr Endpoint,
>             capEPBadge :: Word,
>             capEPCanSend, capEPCanReceive :: Bool,
>             capEPCanGrant, capEPCanGrantReply :: Bool }
>         | DomainCap
>         | Zombie {
>             capZombiePtr :: PPtr CTE,
>             capZombieType :: ZombieType,
>             capZombieNumber :: Int }
>         | ArchObjectCap {
>             capCap :: ArchCapability }
>         | ReplyCap {
>             capTCBPtr :: PPtr TCB,
>             capReplyMaster :: Bool,
>             capReplyCanGrant :: Bool }
>         | UntypedCap {
>             capIsDevice :: Bool,
>             capPtr :: PPtr (),
>             capBlockSize :: Int,
>             capFreeIndex :: Int }
>         | CNodeCap {
>             capCNodePtr :: PPtr CTE,
>             capCNodeBits :: Int,
>             capCNodeGuard :: Word,
>             capCNodeGuardSize :: Int }
>         | IRQControlCap
>         deriving (Eq, Show)

> data ZombieType = ZombieTCB | ZombieCNode { zombieCTEBits :: Int }
>     deriving (Eq, Show)

> isNullCap :: Capability -> Bool
> isNullCap NullCap = True
> isNullCap _ = False

> isDomainCap :: Capability -> Bool
> isDomainCap DomainCap = True
> isDomainCap _ = False

> isIRQControlCap :: Capability -> Bool
> isIRQControlCap IRQControlCap = True
> isIRQControlCap _ = False

> isReplyCap :: Capability -> Bool
> isReplyCap (ReplyCap {}) = True
> isReplyCap _ = False

> isUntypedCap :: Capability -> Bool
> isUntypedCap (UntypedCap {}) = True
> isUntypedCap _ = False

> isNotificationCap :: Capability -> Bool
> isNotificationCap (NotificationCap {}) = True
> isNotificationCap _ = False

\subsection{Kernel Objects}

When stored in the physical memory model (described in \autoref{sec:model.pspace}), kernel objects must be encapsulated in "KernelObject", so the stored type is independent of the real type of the object.

> data KernelObject
>     = KOEndpoint  Endpoint
>     | KONotification Notification
>     | KOKernelData
>     | KOUserData
>     | KOUserDataDevice
>     | KOTCB       TCB
>     | KOCTE       CTE
>     | KOArch      ArchKernelObject

> kernelObjectTypeName :: KernelObject -> String
> kernelObjectTypeName o =
>     case o of
>         KOEndpoint   _ -> "Endpoint"
>         KONotification  _ -> "Notification"
>         KOKernelData   -> "KernelData"
>         KOUserData     -> "UserData"
>         KOUserDataDevice -> "UserDataDevice"
>         KOTCB        _ -> "TCB"
>         KOCTE        _ -> "CTE"
>         KOArch       _ -> "Arch Specific"

> objBitsKO :: KernelObject -> Int
> objBitsKO (KOEndpoint _) = epSizeBits
> objBitsKO (KONotification _) = ntfnSizeBits
> objBitsKO (KOCTE _) = cteSizeBits
> objBitsKO (KOTCB _) = tcbBlockSizeBits
> objBitsKO (KOUserData) = pageBits
> objBitsKO (KOUserDataDevice) = pageBits
> objBitsKO (KOKernelData) = pageBits
> objBitsKO (KOArch a) = archObjSize a

\subsubsection{Synchronous Endpoint}

Synchronous endpoints are represented in the physical memory model
using the "Endpoint" data structure.

> data Endpoint

There are three possible states for a synchronous endpoint:
\begin{itemize}

\item waiting for one or more receive operations to complete, with
a list of pointers to waiting threads.

>         = RecvEP { epQueue :: [PPtr TCB] }

\item idle;

>         | IdleEP

\item or waiting for one or more send operations to complete, with a
list of pointers to waiting threads;

>         | SendEP { epQueue :: [PPtr TCB] }
>     deriving Show

\end{itemize}

\subsubsection{Notification Objects}

Notification objects are represented in the physical memory model
using the "Notification" data structure.

> data NTFN

There are three possible states for a notification:
\begin{itemize}
\item idle;

>         = IdleNtfn

\item active, ready to deliver a notification message consisting of one data word and one message identifier word.

>         | ActiveNtfn { ntfnMsgIdentifier :: Word }

\item or waiting for one or more send operations to complete, with a list of  pointers to the waiting threads;

>         | WaitingNtfn { ntfnQueue :: [PPtr TCB] }
>     deriving Show

> data Notification = NTFN {
>     ntfnObj :: NTFN,
>     ntfnBoundTCB :: Maybe (PPtr TCB) }

\end{itemize}

\subsubsection{Capability Table Entry}

Entries in a capability table node (CNode) are represented by the type
"CTE", an abbreviation of \emph{Capability Table Entry}. Each CTE contains a capability and a mapping database node.

> data CTE = CTE {
>     cteCap :: Capability,
>     cteMDBNode :: MDBNode }
>     deriving Show

\subsubsection{Thread Control Block}

Every thread has a thread control block, allocated by a user-level
server but directly accessible only by the kernel.

> data TCB = Thread {

The TCB is used to store various data about the thread's current state:
\begin{itemize}
\item a slot for a capability to the root node of this thread's address space;

>         tcbCTable :: CTE,

\item a slot for a capability to the root of the thread's page table --- on some architectures, this is a CNode capability, while on others it is a machine-specific type;

>         tcbVTable :: CTE,

\item a slot containing the thread's reply capability, which is never accessed directly in this slot but is used as the MDB parent of the capability generated when this thread performs a "Call";

>         tcbReply :: CTE,

\item a slot that may contain the reply capability of the thread that sent the most recent IPC received by this thread, and is otherwise always empty;

>         tcbCaller :: CTE,

\item a slot that may contain a capability to the frame used for the thread's IPC buffer;

>         tcbIPCBufferFrame :: CTE,

\item the security domain and a flag that determines whether the thread can set the security domain of other threads.

>         tcbDomain :: Domain,

\item the thread's scheduler state and priority;

>         tcbState :: ThreadState,
>         tcbMCP :: Priority,
>         tcbPriority :: Priority,

\item a flag indicating whether the thread is a member of a ready queue.
    Note that the flag is necessary, since although the tcbSchedPrev and tcbSchedNext fields listed below
    are used only to navigate through a ready queue, we cannot say that a thread is queued
    if and only if either its tcbSchedPrev or tcbSchedNext field is not Nothing.
    For consider a thread that is the sole member of a ready queue.
    It will have both its tcbSchedNext and tcbSchedPrev fields equal to Nothing, but it will still be tcbQueued.

>         tcbQueued :: Bool,

\item the thread's current fault state;

>         tcbFault :: Maybe Fault,

\item the amount of time remaining in this thread's timeslice;

>         tcbTimeSlice :: Int,

\item a capability pointer to the fault handler endpoint, which receives an IPC from the kernel whenever this thread generates a fault;

>         tcbFaultHandler :: CPtr,

\item the virtual address of the thread's IPC buffer, which is readable at user level as thread-local data (by an architecture-defined mechanism), and is also used by the kernel to determine the buffer's offset within its frame;

>         tcbIPCBuffer :: VPtr,

\item the thread's currently bound notification object;

>         tcbBoundNotification :: Maybe (PPtr Notification),

\item the thread's pointers to the previous and next entries in a scheduling queue;

>         tcbSchedPrev :: Maybe (PPtr TCB),
>         tcbSchedNext :: Maybe (PPtr TCB),

\item the thread's feature flags, currently only used for fpuDisabled

>         tcbFlags :: TcbFlags,

\item and any arch-specific TCB contents

>         tcbArch :: ArchTCB }
>     deriving Show

\end{itemize}

Each TCB contains four CTE entries. The following constants define the slot numbers in which they will be found if the TCB is treated as a CNode.

> tcbCTableSlot :: Word
> tcbCTableSlot = 0

> tcbVTableSlot :: Word
> tcbVTableSlot = 1

> tcbReplySlot :: Word
> tcbReplySlot = 2

> tcbCallerSlot :: Word
> tcbCallerSlot = 3

> tcbIPCBufferSlot :: Word
> tcbIPCBufferSlot = 4

> minPriority :: Priority
> minPriority = 0

The maximum priority is derived from the configuration parameter "numPriorities".

> maxPriority :: Priority
> maxPriority = fromIntegral (numPriorities - 1)

The maximum domain is derived from the configuration parameter "numDomains"

> maxDomain :: Priority
> maxDomain = fromIntegral (numDomains - 1)

The size of the level 2 bitmap array in each domain.

> l2BitmapSize :: Int
> l2BitmapSize = (numPriorities + wordBits - 1) `div` wordBits

\subsection{Other Types}

\subsubsection{Mapping Database Node}

The mapping database consists of a tree structure for each physical
page that can be mapped at user level. It is used to keep track of all
"CTE"s pointing to each kernel object, so capabilities can be
recursively revoked.

> data MDBNode = MDB {
>     mdbNext, mdbPrev :: PPtr CTE,
>     mdbRevocable, mdbFirstBadged :: Bool }
>     deriving Show

The basic structure is a double-linked list. The algorithm used to determine the mapping hierarchy from this list is described in \autoref{sec:object.cnode.mdb}.

> nullMDBNode :: MDBNode
> nullMDBNode = MDB {
>     mdbNext = nullPointer,
>     mdbPrev = nullPointer,
>     mdbRevocable = False,
>     mdbFirstBadged = False }

\subsubsection{Thread State}

A user thread may be in the following states:

%FIXME: Mangled for datatype constructor order


> data ThreadState

\begin{itemize}

\item blocked on a synchronous IPC send or receive (which require the presence of additional data about the operation);

>     = BlockedOnReceive {
>         blockingObject :: PPtr Endpoint,
>         blockingIPCCanGrant :: Bool }

\item blocked waiting for a reply to a previously sent message;

>     | BlockedOnReply

\item blocked on an notification;

>     | BlockedOnNotification {
>         waitingOnNotification :: PPtr Notification }

\item ready to start executing the next instruction;

>     | Running

\item waiting to be explicitly started;

>     | Inactive

\item or in a special state used only by the idle thread.

>     | IdleThreadState
>     | BlockedOnSend {
>         blockingObject :: PPtr Endpoint,
>         blockingIPCBadge :: Word,
>         blockingIPCCanGrant :: Bool,
>         blockingIPCCanGrantReply :: Bool,
>         blockingIPCIsCall :: Bool }

\item ready to start executing at the current instruction (after a fault, an interrupted system call, or an explicitly set program counter);

>     | Restart
>     deriving (Show, Eq)

\end{itemize}

\subsubsection{Scheduler State}

This type is used to represent the required action, if any, of the scheduler next time it runs.

> data SchedulerAction

\begin{itemize}
\item The normal action of the scheduler before returning to user level is to check that the current thread has a non-zero timeslice, and to choose a new thread otherwise.

>     = ResumeCurrentThread

\item If the current thread is no longer runnable, or a higher priority thread might have been woken, then the scheduler should unconditionally choose a new thread.

>     | ChooseNewThread

\item IPC operations may request that the scheduler switch to a specific thread.

>     | SwitchToThread {
>         schActTarget :: PPtr TCB }

>     deriving (Eq, Show)

\end{itemize}

\subsubsection{Interrupt Controller State}

The interrupt controller state consists of an array with one entry for each of the available IRQs. Each entry contains a pointer to the slot containing the vector's notification endpoint, and a Boolean value that indicates whether any "IRQHandler" object exists for the corresponding IRQ.

> data InterruptState = InterruptState {
>     intStateIRQNode :: PPtr CTE,
>     intStateIRQTable :: Array IRQ IRQState }

> data IRQState
>     = IRQInactive
>     | IRQSignal
>     | IRQTimer
>     | IRQReserved
>     deriving (Show, Eq)

Each entry in the domain schedule specifies a domain and a length (a number of time slices).

> type DomainSchedule = (Domain, Word)
> dschDomain :: (Domain, Word) -> Domain
> dschDomain = fst
> dschLength :: (Domain, Word) -> Word
> dschLength = snd

> isReceive :: ThreadState -> Bool
> isReceive (BlockedOnReceive _ _) = True
> isReceive _ = False

> isSend :: ThreadState -> Bool
> isSend (BlockedOnSend _ _ _ _ _) = True
> isSend _ = False

> isReply :: ThreadState -> Bool
> isReply BlockedOnReply = True
> isReply _ = False

\subsubsection{User Data}

This type is used to represent a frame in the user's address space.

> data UserData = UserData

> data UserDataDevice = UserDataDevice

\subsubsection{The Untyped free index}

Various operations on the free index of an Untyped cap.

> maxFreeIndex :: Int -> Int
> maxFreeIndex sizeBits = bit sizeBits

> getFreeRef :: PPtr () -> Int -> PPtr ()
> getFreeRef base freeIndex = base + (fromIntegral freeIndex)

> getFreeIndex :: PPtr () -> PPtr () -> Int
> getFreeIndex base free = fromIntegral $ fromPPtr (free - base)

> untypedZeroRange :: Capability -> Maybe (Word, Word)
> untypedZeroRange (cap@UntypedCap {}) = if empty || capIsDevice cap
>         then Nothing
>         else Just (fromPPtr startPtr, fromPPtr endPtr)
>     where
>         empty = capFreeIndex cap == maxFreeIndex (capBlockSize cap)
>         startPtr = getFreeRef (capPtr cap) (capFreeIndex cap)
>         endPtr = capPtr cap + PPtr (2 ^ capBlockSize cap) - 1
> untypedZeroRange _ = Nothing

> data TcbQueue = TcbQueue {
>     tcbQueueHead :: Maybe (PPtr TCB),
>     tcbQueueEnd :: Maybe (PPtr TCB) }

> emptyQueue :: TcbQueue
> emptyQueue = TcbQueue { tcbQueueHead = Nothing, tcbQueueEnd = Nothing }

\subsubsection{TCB Flags}

> data TcbFlag = FpuDisabled

> tcbFlagToWord :: TcbFlag -> Word
> tcbFlagToWord (FpuDisabled) = bit 0

Sets of TCB flags are bitwise OR'd and represented as a word.

> type TcbFlags = Word

> noFlag :: TcbFlags
> noFlag = 0x0

> isFlagSet :: TcbFlag -> TcbFlags -> Bool
> isFlagSet flag flags = tcbFlagToWord flag .&. flags /= 0

> tcbFlagMask :: Word
> tcbFlagMask = if config_HAVE_FPU then tcbFlagToWord FpuDisabled else 0
