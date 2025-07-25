%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains the thread control block structure, the TCB invocation operation, and various accessors used by both TCB invocations and the kernel.

\begin{impdetails}

This module uses the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.TCB (
>         threadGet, threadSet, asUser, sanitiseRegister, getSanitiseRegisterInfo,
>         getThreadCSpaceRoot, getThreadVSpaceRoot,
>         getThreadReplySlot, getThreadCallerSlot,
>         getThreadBufferSlot,
>         setupCallerCap, deleteCallerCap,
>         getMRs, setMRs, copyMRs, getMessageInfo, setMessageInfo,
>         tcbFaultHandler, tcbIPCBuffer, tcbTimeSlice,
>         decodeTCBInvocation, invokeTCB,
>         getExtraCPtrs, getExtraCPtr, lookupExtraCaps, setExtraBadge,
>         decodeDomainInvocation,
>         archThreadSet, archThreadGet
>     ) where

\begin{impdetails}

% {-# BOOT-IMPORTS: SEL4.API.Types SEL4.API.Failures SEL4.Machine SEL4.Model SEL4.Object.Structures SEL4.API.Invocation #-}
% {-# BOOT-EXPORTS: threadGet threadSet asUser setMRs setMessageInfo getThreadCSpaceRoot getThreadVSpaceRoot decodeTCBInvocation invokeTCB setupCallerCap getThreadCallerSlot getThreadReplySlot getThreadBufferSlot decodeDomainInvocation archThreadSet archThreadGet sanitiseRegister #-}

> import Prelude hiding (Word)
> import SEL4.Config (numDomains)
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Invocation
> import SEL4.API.InvocationLabels
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.Instances()
> import SEL4.Object.CNode
> import SEL4.Object.ObjectType
> import SEL4.Object.Notification
> import {-# SOURCE #-} SEL4.Kernel.Thread
> import {-# SOURCE #-} SEL4.Kernel.CSpace
> import {-# SOURCE #-} SEL4.Kernel.VSpace

> import Data.Bits
> import Data.Helpers (mapMaybe)
> import Data.List(genericTake, genericLength)
> import Data.Maybe()
> import Data.WordLib
> import Control.Monad.State(runState)

\end{impdetails}

The architecture-specific definitions are imported qualified with the "Arch" prefix.

> import qualified SEL4.Object.TCB.TARGET as Arch

\subsection{Decoding TCB Invocations}

There are eleven types of invocation for a thread control block. All require write permission for the TCB object. In addition, "SetSpace" and "Configure" operations require grant permission. Checking for appropriate permission is done by the caller (see \autoref{sec:object.objecttype}).

> decodeTCBInvocation :: Word -> [Word] -> Capability -> PPtr CTE ->
>         [(Capability, PPtr CTE)] -> KernelF SyscallError TCBInvocation
> decodeTCBInvocation label args cap slot extraCaps =
>     case genInvocationType label of
>         TCBReadRegisters -> decodeReadRegisters args cap
>         TCBWriteRegisters -> decodeWriteRegisters args cap
>         TCBCopyRegisters -> decodeCopyRegisters args cap $ map fst extraCaps
>         TCBSuspend -> return $ Suspend (capTCBPtr cap)
>         TCBResume -> return $ Resume (capTCBPtr cap)
>         TCBConfigure -> decodeTCBConfigure args cap slot extraCaps
>         TCBSetPriority -> decodeSetPriority args cap extraCaps
>         TCBSetMCPriority -> decodeSetMCPriority args cap extraCaps
>         TCBSetSchedParams -> decodeSetSchedParams args cap extraCaps
>         TCBSetIPCBuffer -> decodeSetIPCBuffer args cap slot extraCaps
>         TCBSetSpace -> decodeSetSpace args cap slot extraCaps
>         TCBBindNotification -> decodeBindNotification cap extraCaps
>         TCBUnbindNotification -> decodeUnbindNotification cap
>         TCBSetTLSBase -> decodeSetTLSBase args cap
>         TCBSetFlags -> decodeSetFlags args cap
>         _ -> throw IllegalOperation

\subsubsection{Reading, Writing and Copying Registers}

The kernel provides three methods for accessing the register state of a thread; they read, write, and copy the state of the invoked thread, respectively. The implementations of these methods are in \autoref{sec:object.tcb.invoke.exregs}.

These methods are generally not useful when invoked on the current thread. For registers that are not preserved or read by system calls, unpredictable values will be read from the current thread; any register that is not preserved by a system call will not be successfully written to the current thread. However, the kernel does not prevent such invocations, as doing so would complicate system call monitoring.

Note that the registers copied by "Arch.performTransfer", such as the floating point registers, are always preserved by system calls. Therefore, all three operations can safely read or write those registers when the current thread is the source or destination. It will often be possible to perform such transfers without copying data, because those parts of the context are switched lazily.

The "CopyRegisters" call transfers parts of the user-level context between two different threads, and suspends or resumes each thread. The context is divided into two or more parts, depending on the architecture. The caller is able to select which parts are copied.

> decodeCopyRegisters :: [Word] -> Capability -> [Capability] ->
>         KernelF SyscallError TCBInvocation
> decodeCopyRegisters (flags:_) cap extraCaps = do

The two lowest bits of the flags field are used to determine whether the source thread should be suspended and the destination thread should be resumed, respectively. If either bit is not set, the corresponding thread's scheduler state is not affected.

>     let suspendSource = flags `testBit` 0
>     let resumeTarget = flags `testBit` 1

The remaining bits may used to select which subsets of the register set will be copied. The first two are used for subsets of the integer registers. The first subset includes those which are read, modified or preserved by a system call; they typically include the instruction pointer, stack pointer, message registers, and condition registers. These are defined by the architecture-specific constant "frameRegisters". The second subset contains every other general-purpose integer register, and is defined by the constant "gpRegisters".

>     let transferFrame = flags `testBit` 2
>     let transferInteger = flags `testBit` 3

The bits in the second word of the flags field are used to select architecture-defined subsets of the register set which should be copied. These typically include the register sets of coprocessors, such as floating point and vector units. Registers that may be copied this way should always be preserved by system calls, as discussed above.

>     transferArch <- Arch.decodeTransfer $ fromIntegral $ flags `shiftR` 8

Look up the source capability and check permissions.

>     when (null extraCaps) $ throw TruncatedMessage
>     srcTCB <- case head extraCaps of
>         ThreadCap { capTCBPtr = ptr } ->
>             return ptr
>         _ -> throw $ InvalidCapability 1

>     return CopyRegisters {
>         copyRegsTarget = capTCBPtr cap,
>         copyRegsSource = srcTCB,
>         copyRegsSuspendSource = suspendSource,
>         copyRegsResumeTarget = resumeTarget,
>         copyRegsTransferFrame = transferFrame,
>         copyRegsTransferInteger = transferInteger,
>         copyRegsTransferArch = transferArch }

> decodeCopyRegisters _ _ _ = throw TruncatedMessage

The "ReadRegisters" method copies a subset of the integer registers, stored in seL4 message registers; the "WriteRegisters" method copies the message registers into a subset of the integer registers. In both cases, the registers are transferred in a machine-dependent order, defined by the Haskell expression "frameRegisters ++ gpRegisters". This order is chosen because the registers most likely to be accessed --- the instruction and stack pointers --- are first, followed by the other registers required to checkpoint a thread during a system call, and finally followed by the remaining integer registers. The most common subsets of the register set can therefore be selected by simply truncating the message.

For both of these operations, the first argument is a flags field. The lowest bit of that field, if set, indicates that the invoked thread's state should be changed --- suspending it for a read operation, and resuming it for a write operation. The second byte of the flags field has the same architecture-defined meaning as for "CopyRegisters", assuming a transfer to or from the current thread.

> decodeReadRegisters :: [Word] -> Capability ->
>         KernelF SyscallError TCBInvocation
> decodeReadRegisters (flags:n:_) cap = do
>     rangeCheck n 1 $ length frameRegisters + length gpRegisters
>     transferArch <- Arch.decodeTransfer $ fromIntegral $ flags `shiftR` 8
>     self <- withoutFailure $ getCurThread
>     when (capTCBPtr cap == self) $ throw IllegalOperation
>     return ReadRegisters {
>         readRegsThread = capTCBPtr cap,
>         readRegsSuspend = flags `testBit` 0,
>         readRegsLength = n,
>         readRegsArch = transferArch }
> decodeReadRegisters _ _ = throw TruncatedMessage

> decodeWriteRegisters :: [Word] -> Capability ->
>         KernelF SyscallError TCBInvocation
> decodeWriteRegisters (flags:n:values) cap = do
>     when (genericLength values < n) $ throw TruncatedMessage
>     transferArch <- Arch.decodeTransfer $ fromIntegral $ flags `shiftR` 8
>     self <- withoutFailure $ getCurThread
>     when (capTCBPtr cap == self) $ throw IllegalOperation
>     return WriteRegisters {
>         writeRegsThread = capTCBPtr cap,
>         writeRegsResume = flags `testBit` 0,
>         writeRegsValues = genericTake n values,
>         writeRegsArch = transferArch }
> decodeWriteRegisters _ _ = throw TruncatedMessage

\subsubsection{The Configure Call}

The "Configure" call is a batched call to "SetIPCParams" and "SetSpace".

> decodeTCBConfigure :: [Word] -> Capability -> PPtr CTE ->
>         [(Capability, PPtr CTE)] -> KernelF SyscallError TCBInvocation
> decodeTCBConfigure
>     (faultEP:cRootData:vRootData:buffer:_)
>     cap slot (cRoot:vRoot:bufferFrame:_)
>   = do
>     setIPCParams <- decodeSetIPCBuffer [buffer] cap slot [bufferFrame]
>     setSpace <- decodeSetSpace [faultEP, cRootData, vRootData]
>         cap slot [cRoot, vRoot]
>     return $ ThreadControl {
>         tcThread = capTCBPtr cap,
>         tcThreadCapSlot = tcThreadCapSlot setSpace,
>         tcNewFaultEP = tcNewFaultEP setSpace,
>         tcNewMCPriority = Nothing,
>         tcNewPriority = Nothing,
>         tcNewCRoot = tcNewCRoot setSpace,
>         tcNewVRoot = tcNewVRoot setSpace,
>         tcNewIPCBuffer = tcNewIPCBuffer setIPCParams }
> decodeTCBConfigure _ _ _ _ = throw TruncatedMessage

\subsubsection{Check priorities}

> checkPrio :: Word -> PPtr TCB -> KernelF SyscallError ()
> checkPrio prio auth = do
>     mcp <- withoutFailure $ threadGet tcbMCP auth
>     when (prio > fromIntegral mcp) $ throw (RangeError (fromIntegral minPriority) (fromIntegral mcp))

\subsubsection{The Set Priority Call}

Setting the thread's priority is only allowed if the new priority is lower than or equal to the current thread's. This prevents untrusted clients that hold untyped or TCB capabilities from performing denial of service attacks by creating new maximum-priority threads. This is a temporary solution; there may be significant changes to the scheduler in future versions to provide better partitioning of CPU time.

> decodeSetPriority :: [Word] -> Capability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError TCBInvocation
> decodeSetPriority (newPrio:_) cap ((authCap, _):_) = do
>     authTCB <- case authCap of
>         ThreadCap { capTCBPtr = tcbPtr } -> return tcbPtr
>         _ -> throw $ InvalidCapability 1
>     checkPrio newPrio authTCB
>     return $ ThreadControl {
>         tcThread = capTCBPtr cap,
>--       tcThreadCapSlot = error "tcThreadCapSlot unused", In theory tcThreadCapSlot should never been evaluated by lazy evaluation. However, it was evaluated when running sel4 haskell kernel. So it is wired. Thus I change this to 0. I hope this can be changed back once we find out why this is evaluated. (by Xin)
>         tcThreadCapSlot = 0,
>         tcNewFaultEP = Nothing,
>         tcNewMCPriority = Nothing,
>         tcNewPriority = Just $ (fromIntegral newPrio, authTCB),
>         tcNewCRoot = Nothing,
>         tcNewVRoot = Nothing,
>         tcNewIPCBuffer = Nothing }
> decodeSetPriority _ _ _ = throw TruncatedMessage

> decodeSetMCPriority :: [Word] -> Capability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError TCBInvocation
> decodeSetMCPriority (newMCP:_) cap ((authCap, _):_) = do
>     authTCB <- case authCap of
>         ThreadCap { capTCBPtr = tcbPtr } -> return tcbPtr
>         _ -> throw $ InvalidCapability 1
>     checkPrio newMCP authTCB
>     return $ ThreadControl {
>         tcThread = capTCBPtr cap,
>         tcThreadCapSlot = 0,
>         tcNewFaultEP = Nothing,
>         tcNewMCPriority = Just $ (fromIntegral newMCP, authTCB),
>         tcNewPriority = Nothing,
>         tcNewCRoot = Nothing,
>         tcNewVRoot = Nothing,
>         tcNewIPCBuffer = Nothing }
> decodeSetMCPriority _ _ _ = throw TruncatedMessage

The "SetSchedParams" call sets both the priority and the MCP in a single call.

> decodeSetSchedParams :: [Word] -> Capability -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError TCBInvocation
> decodeSetSchedParams (newMCP:newPrio:_) cap ((authCap, _):_) = do
>     authTCB <- case authCap of
>         ThreadCap { capTCBPtr = tcbPtr } -> return tcbPtr
>         _ -> throw $ InvalidCapability 1
>     checkPrio newMCP authTCB
>     checkPrio newPrio authTCB
>     return $ ThreadControl {
>         tcThread = capTCBPtr cap,
>         tcThreadCapSlot = 0,
>         tcNewFaultEP = Nothing,
>         tcNewMCPriority = Just $ (fromIntegral newMCP, authTCB),
>         tcNewPriority = Just $ (fromIntegral newPrio, authTCB),
>         tcNewCRoot = Nothing,
>         tcNewVRoot = Nothing,
>         tcNewIPCBuffer = Nothing }
> decodeSetSchedParams _ _ _ = throw TruncatedMessage

\subsubsection{The Set IPC Buffer Call}

The two thread parameters related to IPC and system call handling are the IPC buffer pointer, and a capability to access the frame containing the buffer. The kernel uses the virtual address to determine the buffer's location in the frame, and also exposes it to the thread in a well-defined location; it does not necessarily ensure that the buffer frame is actually mapped at the given address. There may be architecture-defined requirements for the pointer and frame capability; typically the only requirement is that the buffer fits inside the given frame.

> decodeSetIPCBuffer :: [Word] -> Capability -> PPtr CTE ->
>         [(Capability, PPtr CTE)] -> KernelF SyscallError TCBInvocation
> decodeSetIPCBuffer (bufferPtr:_) cap slot ((bufferCap, bufferSlot):_) = do
>     let ipcBuffer = VPtr bufferPtr
>     bufferFrame <- if ipcBuffer == 0
>         then return Nothing
>         else do
>             bufferCap' <- deriveCap bufferSlot bufferCap
>             checkValidIPCBuffer ipcBuffer bufferCap'
>             return $ Just (bufferCap', bufferSlot)
>     return $ ThreadControl {
>         tcThread = capTCBPtr cap,
>         tcThreadCapSlot = slot,
>         tcNewFaultEP = Nothing,
>         tcNewMCPriority = Nothing,
>         tcNewPriority = Nothing,
>         tcNewCRoot = Nothing,
>         tcNewVRoot = Nothing,
>         tcNewIPCBuffer = Just (ipcBuffer, bufferFrame) }
> decodeSetIPCBuffer _ _ _ _ = throw TruncatedMessage

\subsubsection{The Set Space Call}
\label{sec:object.tcb.decode.setspace}

Setting the capability space and virtual address space roots is similar to a pair of CNode Insert operation, except that any previous root is implicitly deleted rather than causing an error, and the new roots must be valid capabilities of the appropriate types. The fault endpoint, like the result endpoint, is not checked for validity at this point; messages sent to it will be silently dropped if it is not valid.

If an existing root capability is valid and final --- that is, it is the only existing capability for the root object --- then it cannot be changed with this call.
\begin{impdetails}
This is to ensure that the source capability is not made invalid by the deletion of the old root.
\end{impdetails}

> decodeSetSpace :: [Word] -> Capability -> PPtr CTE ->
>         [(Capability, PPtr CTE)] -> KernelF SyscallError TCBInvocation
> decodeSetSpace (faultEP:cRootData:vRootData:_) cap slot (cRootArg:vRootArg:_)
>         = do
>     canChangeCRoot <- withoutFailure $ liftM not $
>         slotCapLongRunningDelete =<< getThreadCSpaceRoot (capTCBPtr cap)
>     canChangeVRoot <- withoutFailure $ liftM not $
>         slotCapLongRunningDelete =<< getThreadVSpaceRoot (capTCBPtr cap)
>     unless (canChangeCRoot && canChangeVRoot) $
>         throw IllegalOperation
>     let (cRootCap, cRootSlot) = cRootArg
>     cRootCap' <- deriveCap cRootSlot $ if cRootData == 0
>         then cRootCap
>         else updateCapData False cRootData cRootCap
>     cRoot <- case cRootCap' of
>         CNodeCap {} -> return (cRootCap', cRootSlot)
>         _ -> throw IllegalOperation
>     let (vRootCap, vRootSlot) = vRootArg
>     vRootCap' <- deriveCap vRootSlot $ if vRootData == 0
>         then vRootCap
>         else updateCapData False vRootData vRootCap
>     vRoot <- if isValidVTableRoot vRootCap'
>         then return (vRootCap', vRootSlot)
>         else throw IllegalOperation
>     return $ ThreadControl {
>         tcThread = capTCBPtr cap,
>         tcThreadCapSlot = slot,
>         tcNewFaultEP = Just $ CPtr faultEP,
>         tcNewMCPriority = Nothing,
>         tcNewPriority = Nothing,
>         tcNewCRoot = Just cRoot,
>         tcNewVRoot = Just vRoot,
>         tcNewIPCBuffer = Nothing }
> decodeSetSpace _ _ _ _ = throw TruncatedMessage

\subsubsection{Decode Bound Notification Invocations}

> decodeBindNotification :: Capability -> [(Capability, PPtr CTE)] -> KernelF SyscallError TCBInvocation
> decodeBindNotification cap extraCaps = do
>     -- if no notification cap supplied
>     when (null extraCaps) $ throw TruncatedMessage
>     let tcb = capTCBPtr cap
>     ntfn <- withoutFailure $ getBoundNotification tcb
>     -- check if tcb already has bound notification
>     case ntfn of
>         Just _ -> throw IllegalOperation
>         Nothing -> return ()
>     -- get ptr to notification
>     (ntfnPtr, rights) <- case fst (head extraCaps) of
>         NotificationCap ptr _ _ recv  -> return (ptr, recv)
>         _ -> throw IllegalOperation
>     when (not rights) $ throw IllegalOperation
>     -- check if notification is bound
>     -- check if anything is waiting on the notification
>     notification <- withoutFailure $ getNotification ntfnPtr
>     case (ntfnObj notification, ntfnBoundTCB notification) of
>         (IdleNtfn, Nothing) -> return ()
>         (ActiveNtfn _, Nothing) -> return ()
>         _ -> throw IllegalOperation
>     return NotificationControl {
>         notificationTCB = tcb,
>         notificationPtr = Just ntfnPtr }


> decodeUnbindNotification :: Capability -> KernelF SyscallError TCBInvocation
> decodeUnbindNotification cap = do
>     let tcb = capTCBPtr cap
>     ntfn <- withoutFailure $ getBoundNotification tcb
>     case ntfn of
>         Nothing -> throw IllegalOperation
>         Just _ -> return ()
>     return NotificationControl {
>         notificationTCB = tcb,
>         notificationPtr = Nothing }

> decodeSetTLSBase :: [Word] -> Capability ->
>         KernelF SyscallError TCBInvocation
> decodeSetTLSBase (tls_base:_) cap = do
>     return $ SetTLSBase {
>         setTLSBaseTCB = capTCBPtr cap,
>         setTLSBaseNewBase = tls_base }
> decodeSetTLSBase _ _ = throw TruncatedMessage

> decodeSetFlags :: [Word] -> Capability ->
>         KernelF SyscallError TCBInvocation
> decodeSetFlags (flagsClear:flagsSet:_) cap = do
>     return $ SetFlags {
>         setFlagsTCB = capTCBPtr cap,
>         setFlagsClear = flagsClear,
>         setFlagsSet = flagsSet }
> decodeSetFlags _ _ = throw TruncatedMessage

\subsection[invoke]{Performing TCB Invocations}

> invokeTCB :: TCBInvocation -> KernelP [Word]

\subsubsection{Scheduler Operations}

The "Suspend" and "Resume" calls are simple scheduler operations.

> invokeTCB (Suspend thread) =
>     withoutPreemption $ do
>         suspend thread
>         return []
> invokeTCB (Resume thread) =
>     withoutPreemption $ do
>         restart thread
>         return []

\subsubsection{Thread Control Operations}

The "ThreadControl" operation is used to implement the "SetSpace", "SetPriority", "SetIPCParams" and "Configure" methods.

The use of "checkCapAt" addresses a corner case in which the only capability to a certain thread is in its own CSpace, which is otherwise unreachable. Replacement of the CSpace root results in "cteDelete" cleaning up both CSpace and thread, after which "cteInsert" should not be called. Error reporting in this case is unimportant, as the requesting thread cannot continue to execute.

> invokeTCB (ThreadControl target slot faultep mcp priority cRoot vRoot buffer)
>   = do
>         let tCap = ThreadCap { capTCBPtr = target }
>         withoutPreemption $ maybe (return ())
>             (\ep -> threadSet (\t -> t {tcbFaultHandler = ep}) target)
>             faultep
>         withoutPreemption $ maybe (return ()) (setMCPriority target) (mapMaybe fst mcp)
>         maybe (return ()) (\(newCap, srcSlot) -> do
>             rootSlot <- withoutPreemption $ getThreadCSpaceRoot target
>             cteDelete rootSlot True
>             withoutPreemption
>                 $ checkCapAt newCap srcSlot
>                 $ checkCapAt tCap slot
>                 $ assertDerived srcSlot newCap
>                 $ cteInsert newCap srcSlot rootSlot)
>           cRoot
>         maybe (return ()) (\(newCap, srcSlot) -> do
>             rootSlot <- withoutPreemption $ getThreadVSpaceRoot target
>             cteDelete rootSlot True
>             withoutPreemption
>                 $ checkCapAt newCap srcSlot
>                 $ checkCapAt tCap slot
>                 $ assertDerived srcSlot newCap
>                 $ cteInsert newCap srcSlot rootSlot)
>           vRoot
>         maybe (return ())
>             (\(ptr, frame) -> do
>                 bufferSlot <- withoutPreemption $ getThreadBufferSlot target
>                 cteDelete bufferSlot True
>                 withoutPreemption $ threadSet
>                     (\t -> t {tcbIPCBuffer = ptr}) target
>                 withoutPreemption $ case frame of
>                     Just (newCap, srcSlot) ->
>                         checkCapAt newCap srcSlot
>                             $ checkCapAt tCap slot
>                             $ assertDerived srcSlot newCap
>                             $ cteInsert newCap srcSlot bufferSlot
>                     Nothing -> return ()
>                 thread <- withoutPreemption $ getCurThread
>                 withoutPreemption $ when (target == thread) $ rescheduleRequired)
>             buffer
>         withoutPreemption $ maybe (return ()) (setPriority target) (mapMaybe fst priority)
>         return []

\subsubsection{Register State}
\label{sec:object.tcb.invoke.exregs}

There are three operations that read or write register state. The most general is "CopyRegisters", which transfers subsets of the register state from one specified thread to another.

> invokeTCB (CopyRegisters dest src suspendSource resumeTarget
>         transferFrame transferInteger transferArch)
>   = withoutPreemption $ do

The source is suspended and the destination resumed, if requested.

>     when suspendSource $ suspend src
>     when resumeTarget $ restart dest

Transfer the frame registers.

>     when transferFrame $ do
>         mapM_ (\r -> do
>                 v <- asUser src $ getRegister r
>                 asUser dest $ setRegister r v)
>             frameRegisters

The target thread's program counter has been modified. Ensure that the thread will restart at that address.

>         pc <- asUser dest getRestartPC
>         asUser dest $ setNextPC pc

Transfer the other integer registers.

>     when transferInteger $ do
>         mapM_ (\r -> do
>                 v <- asUser src $ getRegister r
>                 asUser dest $ setRegister r v)
>             gpRegisters


Perform any arch-specific register cleanup or notifications

>     thread <- getCurThread
>     asUser dest $ Arch.postModifyRegisters thread dest

Modifying the current thread may require rescheduling because modified registers are only reloaded in Arch\_switchToThread

>     when (dest == thread) $ rescheduleRequired

At this point, implementations may copy any registers indicated by the two implementation-defined transfer flags.

>     Arch.performTransfer transferArch src dest
>     return []

The "ReadRegisters" and "WriteRegisters" functions are similar to "CopyRegisters", but use an IPC message as the destination or source of the transfer, respectively.

> invokeTCB (ReadRegisters src suspendSource n arch) =
>   withoutPreemption $ do
>     when suspendSource $ suspend src
>     self <- getCurThread
>     Arch.performTransfer arch src self
>     let regs = genericTake n $ frameRegisters ++ gpRegisters
>     asUser src $ mapM getRegister regs

> invokeTCB (WriteRegisters dest resumeTarget values arch) =
>   withoutPreemption $ do
>     self <- getCurThread
>     Arch.performTransfer arch self dest
>     t <- getSanitiseRegisterInfo dest
>     asUser dest $ do
>         zipWithM (\r v -> setRegister r (sanitiseRegister t r v))
>             (frameRegisters ++ gpRegisters) values
>         pc <- getRestartPC
>         setNextPC pc
>     asUser dest $ Arch.postModifyRegisters self dest
>     when resumeTarget $ restart dest

Modifying the current thread may require rescheduling because modified registers are only reloaded in Arch\_switchToThread

>     when (dest == self) $ rescheduleRequired
>     return []

\subsubsection{Invoking Notication Control}

> -- notes: we know that the notification is not bound, and is not waiting.
> -- BIND
> invokeTCB (NotificationControl tcb (Just ntfnPtr)) =
>   withoutPreemption $ do
>     bindNotification tcb ntfnPtr
>     return []

> -- UNBIND
> invokeTCB (NotificationControl tcb Nothing) =
>   withoutPreemption $ do
>     unbindNotification tcb
>     return []

> invokeTCB (SetTLSBase tcb tls_base) =
>   withoutPreemption $ do
>     asUser tcb $ setRegister tlsBaseRegister tls_base
>     cur <- getCurThread
>     when (tcb == cur) rescheduleRequired
>     return []

> invokeTCB (SetFlags tcb flagsClear flagsSet) =
>   withoutPreemption $ do
>     newFlags <- invokeSetFlags tcb flagsClear flagsSet
>     return [newFlags]

> invokeSetFlags :: PPtr TCB -> Word -> Word -> Kernel Word
> invokeSetFlags tcb flagsClear flagsSet = do
>     flags <- threadGet tcbFlags tcb
>     let newFlags = (flags .&. complement flagsClear) .|. (flagsSet .&. tcbFlagMask)
>     setFlags tcb newFlags
>     Arch.postSetFlags tcb newFlags
>     return newFlags

\subsection{Decoding Domain Invocations}

The domain cap is invoked to set the domain of a given TCB object to a given value.

> decodeDomainInvocation :: Word -> [Word] -> [(Capability, PPtr CTE)] ->
>         KernelF SyscallError (PPtr TCB, Domain)
> decodeDomainInvocation label args extraCaps = do
>     when (genInvocationType label /= DomainSetSet) $ throw IllegalOperation
>     domain <- case args of
>         (x:_) -> do
>                      when (fromIntegral x >= numDomains) $
>                          throw InvalidArgument { invalidArgumentNumber = 0 }
>                      return $ fromIntegral x
>         _ -> throw TruncatedMessage
>     when (null extraCaps) $ throw TruncatedMessage
>     case fst (head extraCaps) of
>         ThreadCap { capTCBPtr = ptr } -> return $ (ptr, domain)
>         _ -> throw InvalidArgument { invalidArgumentNumber = 1 }

\subsection{Checks}

The "checkCapAt" function ensures that a capability of the same type and object reference remains at a given slot. It is used by the "ThreadControl" invocation, defined above.

> checkCapAt :: Capability -> PPtr CTE -> Kernel () -> Kernel ()
> checkCapAt cap ptr action = do
>         cap' <- liftM cteCap $ getCTE ptr
>         when (sameObjectAs cap cap') action

This function is similar to stateAssert and used in invokeTCB above. It asserts a state dependent condition that is just True in Haskell, but more complex in the Isabelle translation, and afterwards executes the specified function.

> assertDerived :: PPtr CTE -> Capability -> Kernel a -> Kernel a
> assertDerived _ _ f = f

\subsection{Messages}

\subsubsection{Message Parameters}

The following two functions get and set the message information register for the given thread.

> setMessageInfo :: PPtr TCB -> MessageInfo -> Kernel ()
> setMessageInfo thread info = do
>         let x = wordFromMessageInfo info
>         asUser thread $ setRegister msgInfoRegister x

> getMessageInfo :: PPtr TCB -> Kernel MessageInfo
> getMessageInfo thread = do
>         x <- asUser thread $ getRegister msgInfoRegister
>         return $ messageInfoFromWord x

\subsubsection{Message Data}

The following functions get or set a thread's message data, given a pointer to a TCB and a pointer to the start of the thread's IPC buffer.

These functions assume that the buffer is large enough to store all MRs without crossing any page boundaries.

The "setMRs" function returns the number of words of message data successfully transferred.

> setMRs :: PPtr TCB -> Maybe (PPtr Word) -> [Word] -> Kernel Word
> setMRs thread buffer messageData = do
>         let intSize = fromIntegral wordSize
>         let hardwareMRs = msgRegisters
>         let bufferMRs = case buffer of
>                 Just bufferPtr ->
>                     map (\x -> bufferPtr +
>                             PPtr (x*intSize))
>                         [fromIntegral $ length hardwareMRs+1 .. msgMaxLength]
>                 Nothing -> []
>         let msgLength = min
>                 (length messageData)
>                 (length hardwareMRs + length bufferMRs)
>         let mrs = take msgLength messageData
>         asUser thread $ zipWithM_ setRegister hardwareMRs mrs
>         zipWithM_ storeWordUser bufferMRs $ drop (length hardwareMRs) mrs
>         return $ fromIntegral msgLength

> getMRs :: PPtr TCB -> Maybe (PPtr Word) -> MessageInfo ->
>         Kernel [Word]
> getMRs thread buffer info = do
>         let intSize = fromIntegral wordSize
>         let hardwareMRs = msgRegisters
>         hardwareMRValues <- asUser thread $ mapM getRegister hardwareMRs
>         bufferMRValues <- case buffer of
>             Just bufferPtr -> do
>                 let bufferMRs = map (\x -> bufferPtr +
>                             PPtr (x*intSize))
>                         [fromIntegral $ length hardwareMRs+1.. msgMaxLength]
>                 mapM loadWordUser bufferMRs
>             Nothing -> return []
>         let values = hardwareMRValues ++ bufferMRValues
>         return $ take (fromIntegral $ msgLength info) values

In order to correctly model a C implementation's behaviour when IPC buffers overlap, we have a third function "copyMRs", which reads from one thread's message registers and writes to another thread's. In most cases, this is equivalent to "getMRs sender >>= setMRs receiver". The results will only be different in the case that the IPC buffers overlap (which is not sensible behaviour, but doesn't harm the kernel and can't easily be prevented).

This function's first argument is the maximum number of message registers to copy; it returns the number that were actually copied.

> copyMRs :: PPtr TCB -> Maybe (PPtr Word) ->
>            PPtr TCB -> Maybe (PPtr Word) ->
>            Word -> Kernel Word
> copyMRs sender sendBuf receiver recvBuf n = do
>         let intSize = fromIntegral wordSize
>         let hardwareMRs = take (fromIntegral n) msgRegisters
>         forM hardwareMRs $ \r -> do
>             v <- asUser sender $ getRegister r
>             asUser receiver $ setRegister r v
>         bufferMRs <- case (sendBuf, recvBuf) of
>             (Just sbPtr, Just rbPtr) ->
>                 mapM (\x -> do
>                     v <- loadWordUser (sbPtr + PPtr (x*intSize))
>                     storeWordUser (rbPtr + PPtr (x*intSize)) v
>                 ) [fromIntegral $ length msgRegisters+1 .. n]
>             _ -> return []
>         return $ min n $ fromIntegral $ length hardwareMRs + length bufferMRs

\subsubsection{Extra Capabilities}

The following functions read and set the extra capability fields of the IPC buffer. On sending, these fields are treated as capability pointers; on receiving, they are badges taken from capabilities to the receive endpoint.

> getExtraCPtrs :: Maybe (PPtr Word) -> MessageInfo ->
>         Kernel [CPtr]
> getExtraCPtrs buffer (MI { msgExtraCaps = count }) = do
>         let intSize = fromIntegral wordSize
>         case buffer of
>             Just bufferPtr -> do
>                 let offset = msgMaxLength+1
>                 let bufferPtrs = map (\x -> bufferPtr +
>                         PPtr ((x+offset)*intSize)) [1, 2 .. count]
>                 mapM (liftM CPtr . loadWordUser) bufferPtrs
>             Nothing -> return []

> lookupExtraCaps :: PPtr TCB -> Maybe (PPtr Word) -> MessageInfo ->
>         KernelF Fault [(Capability, PPtr CTE)]
> lookupExtraCaps thread buffer info = do
>         cptrs <- withoutFailure $ getExtraCPtrs buffer info
>         mapM (\cptr ->
>           capFaultOnFailure cptr False $ lookupCapAndSlot thread cptr) cptrs

The next function is for convenience in transferCapsLoop. It is equivalent in
the sense that
getExtraCPtrs (Some buffer) (MI { msgExtraCaps = count }) =
mapM (getExtraCPtr buffer) [0..count-1]

> getExtraCPtr :: PPtr Word -> Int -> Kernel CPtr
> getExtraCPtr buffer n = do
>         let intSize = fromIntegral wordSize
>         let ptr = buffer + bufferCPtrOffset +
>                   PPtr ((fromIntegral n) * intSize)
>         cptr <- loadWordUser ptr
>         return $ CPtr cptr

Write the unwrapped badge into the IPC buffer for cap n.

> setExtraBadge :: PPtr Word -> Word -> Int -> Kernel ()
> setExtraBadge buffer badge n = do
>         let intSize = fromIntegral wordSize
>         let badgePtr = buffer + bufferCPtrOffset +
>                        PPtr ((fromIntegral n) * intSize)
>         storeWordUser badgePtr badge

> bufferCPtrOffset :: PPtr Word
> bufferCPtrOffset =
>         let intSize = fromIntegral wordSize
>         in PPtr ((msgMaxLength+2)*intSize)

\subsection{Creating and Destroying the Caller Capability}

When a message is transferred after a "Call" operation or a fault, the kernel places a reply capability in a special slot in the receiver's TCB. The receiver may use the "Reply" operation to respond to the message and resume execution of the caller or faulting thread.

> setupCallerCap :: PPtr TCB -> PPtr TCB -> Bool -> Kernel ()
> setupCallerCap sender receiver canGrant = do
>     setThreadState BlockedOnReply sender
>     replySlot <- getThreadReplySlot sender
>     masterCTE <- getCTE replySlot
>     let masterCap = cteCap masterCTE
>     assert (isReplyCap masterCap && capReplyMaster masterCap &&
>             capTCBPtr masterCap == sender)
>         "Sender must have a valid reply master cap"
>     assert (mdbNext (cteMDBNode masterCTE) == nullPointer)
>         "Sender must not already have reply cap issued"
>     callerSlot <- getThreadCallerSlot receiver
>     callerCap <- getSlotCap callerSlot
>     assert (isNullCap callerCap)
>         "Caller cap must not already exist"
>     cteInsert (ReplyCap sender False canGrant) replySlot callerSlot

When a new "Recv" operation begins, the caller slot in the waiting thread's TCB is cleared. This removes any ambiguity about the source of the capability in the caller slot: if one is present, it was always generated by the most recent "Recv".

> deleteCallerCap :: PPtr TCB -> Kernel ()
> deleteCallerCap receiver = do
>     callerSlot <- getThreadCallerSlot receiver
>     callerCap <- getSlotCap callerSlot
>     assert (isReplyCap callerCap || isNullCap callerCap)
>         "Caller cap must be a reply cap"
>     cteDeleteOne callerSlot

\subsection{TCB Accessors}

\subsubsection{Address Space Accesses}

This function will return a physical pointer to a thread's root capability table entry, given a pointer to its "TCB".

> getThreadCSpaceRoot :: PPtr TCB -> Kernel (PPtr CTE)
> getThreadCSpaceRoot thread = do
>         locateSlotTCB thread tcbCTableSlot

This function will return a physical pointer to a thread's page table root, given a pointer to its "TCB".

> getThreadVSpaceRoot :: PPtr TCB -> Kernel (PPtr CTE)
> getThreadVSpaceRoot thread = locateSlotTCB thread tcbVTableSlot

This function will return a physical pointer to a thread's reply slot, which is used when creating or revoking its reply capability.

> getThreadReplySlot :: PPtr TCB -> Kernel (PPtr CTE)
> getThreadReplySlot thread = locateSlotTCB thread tcbReplySlot

This function will return a physical pointer to a thread's caller slot, used by the "Call" and "Reply" system calls.

> getThreadCallerSlot :: PPtr TCB -> Kernel (PPtr CTE)
> getThreadCallerSlot thread = locateSlotTCB thread tcbCallerSlot

This function will return a physical pointer to a thread's IPC buffer slot, used to quickly access the thread's IPC buffer.

> getThreadBufferSlot :: PPtr TCB -> Kernel (PPtr CTE)
> getThreadBufferSlot thread = locateSlotTCB thread tcbIPCBufferSlot

\subsubsection{Fetching or Modifying TCB Fields}

The following two trivial functions will get or set a given field of a
TCB, using a pointer to the TCB.

> threadGet :: (TCB-> a) -> PPtr TCB -> Kernel a
> threadGet f tptr = liftM f $ getObject tptr

> threadSet :: (TCB -> TCB) -> PPtr TCB -> Kernel ()
> threadSet f tptr = do
>         tcb <- getObject tptr
>         setObject tptr $ f tcb

For convenience, we create analogous functions for a TCBs arch component.

> archThreadGet :: (ArchTCB -> a) -> PPtr TCB -> Kernel a
> archThreadGet f tptr = liftM (f . tcbArch) $ getObject tptr

> archThreadSet :: (ArchTCB -> ArchTCB) -> PPtr TCB -> Kernel ()
> archThreadSet f tptr = do
>         tcb <- getObject tptr
>         setObject tptr $ tcb { tcbArch = f (tcbArch tcb) }

\subsection{User-level Context}

Actions performed by user-level code, or by the kernel when modifying
the user-level context of a thread, access only the "UserContext"
structure in the thread's TCB.

The following function performs an operation in the user-level context of a specified
thread. The operation is represented by a function in the
"State" monad operating on the thread's "UserContext" structure.

A typical use of this function is "asUser tcbPtr \$ setRegister R0 1",
which stores the value "1" in the register "R0" of to the thread
identified by "tcbPtr".

> asUser :: PPtr TCB -> UserMonad a -> Kernel a
> asUser tptr f = do
>         uc <- threadGet (atcbContextGet . tcbArch) tptr
>         let (a, uc') = runState f $ uc
>         threadSet (\tcb -> tcb { tcbArch = atcbContextSet uc' (tcbArch tcb) }) tptr
>         return a

On some architectures, the thread context may include registers that may be modified by user level code, but cannot safely be given arbitrary values. For example, some of the bits in the ARM architecture's CPSR are used for conditional execution, and others enable kernel mode. This function is used to filter out any bits that should not be modified by user level programs.

> sanitiseRegister :: Bool -> Register -> Word -> Word
> sanitiseRegister t (Register r) (Word w) = Word $ Arch.sanitiseRegister t r w

> getSanitiseRegisterInfo :: PPtr TCB -> Kernel Bool
> getSanitiseRegisterInfo t = Arch.getSanitiseRegisterInfo t

