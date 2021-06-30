%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines several functions operating on kernel objects. These operations are applicable to all objects, but have implementations specific to each object type. These functions are partly implementation-defined, as they may operate on implementation-defined object types.

\begin{impdetails}

We use the C preprocessor to select a target architecture.

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.Object.ObjectType where

\begin{impdetails}

> {-# BOOT-IMPORTS: SEL4.Machine SEL4.API.Types SEL4.Model SEL4.Object.Structures #-}
> {-# BOOT-EXPORTS: createObject #-}

> import Prelude hiding (Word)
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Invocation
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.Instances()
> import SEL4.Object.SchedContext
> import SEL4.Object.Untyped
> import SEL4.Object.Endpoint
> import SEL4.Object.Notification
> import SEL4.Object.Interrupt
> import SEL4.Object.Reply
> import {-# SOURCE #-} SEL4.Object.CNode
> import {-# SOURCE #-} SEL4.Object.TCB
> import {-# SOURCE #-} SEL4.Kernel.Thread

> import Data.Bits
> import Data.WordLib
> import Data.Maybe(fromJust)

\end{impdetails}

The architecture-specific definitions are imported qualified with the "Arch" prefix.

> import qualified SEL4.Object.ObjectType.TARGET as Arch

\subsection{Creating Capabilities}

When copying a capability, it may be necessary to reset or modify data that is specific to each capability (rather than to each object). The following function is used when copying a capability, to allow such changes.

> deriveCap :: PPtr CTE -> Capability -> KernelF SyscallError Capability

Zombie capabilities refer to objects that are in the process of being destroyed because a thread has requested deletion of their last remaining capability (ie, this one). Copying them is not allowed.

> deriveCap _ (Zombie {}) = return NullCap

There may be at most one IRQ control capability in the system, it cannot be copied.

> deriveCap _ (IRQControlCap) = return NullCap

Untyped capabilities cannot be copied if they have children.

> deriveCap slot cap@(UntypedCap {}) = do
>     ensureNoChildren slot
>     return cap

Architecture-specific capability types are handled in the relevant module.

> deriveCap slot (ArchObjectCap cap) =
>     Arch.deriveCap slot cap

Other capabilities do not require modification.

> deriveCap _ cap = return cap

The conditions required for a capability to be marked as "revocable"

> isCapRevocable :: Capability -> Capability -> Bool
> isCapRevocable newCap srcCap = case newCap of

Some arch capabilities can be marked revocable.

>     ArchObjectCap {} -> Arch.isCapRevocable newCap srcCap

If the new capability is an endpoint capability, then it can be an MDB parent if and only if its badge is being changed by this operation.

>     EndpointCap {} -> capEPBadge newCap /= capEPBadge srcCap
>     NotificationCap {} -> capNtfnBadge newCap /= capNtfnBadge srcCap

If the new capability is the first IRQ handler for a given IRQ, then it can be an MDB parent.

>     IRQHandlerCap {} -> isIRQControlCap srcCap

Untyped capabilities can always be MDB parents.

>     UntypedCap {} -> True

Any other capability created by this function is a leaf of the derivation tree, and cannot be used to revoke other capabilities.

>     _ -> False



\subsection{Finalising Capabilities}
\label{sec:object.objecttype.finalise}

Similarly, when deleting a capability, it may be necessary to change other parts of the kernel or machine state that refer to that specific capability. If the deleted capability is the last one referring to the object, it is also necessary to clean up any references to the object itself.

The "finaliseCap" operation takes any finalisation actions that need to be taken before this capability can be deleted. The first boolean flag indicates whether this is the final capability to an object. A special case is when the capability refers to other capability slots. If these need to be cleared, we have a recursive problem which may take unbounded time to resolve. The second flag asserts that the capability being passed is not of a type that can cause such recursion.

During the unbounded capability clearing operation, the capability to the slots is replaced by a "Zombie" capability which records which slots remain to be cleared but cannot be invoked, traversed or copied. This case is handled here by returning the "Zombie" which will be inserted. The "Zombie" finalisation process is handled elsewhere (see "finaliseSlot", \autoref{sec:object.cnode.ops.delete}).

> finaliseCap :: Capability -> Bool -> Bool -> Kernel (Capability, Capability)

When the last capability to an endpoint is deleted, any IPC operations currently using it are aborted.

> finaliseCap (EndpointCap { capEPPtr = ptr }) final _ = do
>     when final $ cancelAllIPC ptr
>     return (NullCap, NullCap)

> finaliseCap (NotificationCap { capNtfnPtr = ptr }) final _ = do
>     when final $ do
>         schedContextMaybeUnbindNtfn ptr
>         unbindMaybeNotification ptr
>         cancelAllSignals ptr
>     return (NullCap, NullCap)

> finaliseCap (ReplyCap { capReplyPtr = ptr }) final _ = do
>     when final $ do
>         stateAssert sym_refs_asrt
>             "Assert that `sym_refs (state_refs_of' s)` holds"
>         stateAssert (valid_replies'_sc_asrt ptr)
>             "Assert that `valid_replies'` holds"
>         tptrOpt <- liftM replyTCB (getReply ptr)
>         when (tptrOpt /= Nothing) $ do
>             replyClear ptr (fromJust tptrOpt)
>     return (NullCap, NullCap)

No action need be taken for Null or Domain capabilities.

> finaliseCap NullCap _ _ = return (NullCap, NullCap)
> finaliseCap DomainCap _ _ = return (NullCap, NullCap)

Capabilities other than the above should never be passed with the second boolean flag set.

> finaliseCap _ _ True = fail "finaliseCap: failed to finalise immediately."

A "CNodeCap" is replaced with the appropriate "Zombie". No other action is needed.

> finaliseCap (CNodeCap { capCNodePtr = ptr, capCNodeBits = bits }) True _ =
>     return (Zombie ptr (ZombieCNode bits) (bit bits), NullCap)

Threads are treated as special capability nodes; they also become zombies when their final capabilities are deleted, but they must first be suspended to prevent them being scheduled during deletion.

> finaliseCap (ThreadCap { capTCBPtr = tptr}) True _ = do
>     cte_ptr <- getThreadCSpaceRoot tptr
>     unbindNotification tptr
>     unbindFromSC tptr
>     suspend tptr
>     Arch.prepareThreadDelete tptr
>     return (Zombie cte_ptr ZombieTCB 5, NullCap)

> finaliseCap (SchedContextCap { capSchedContextPtr = scPtr }) True _ = do
>     schedContextUnbindAllTCBs scPtr
>     schedContextUnbindNtfn scPtr
>     schedContextUnbindReply scPtr
>     schedContextUnbindYieldFrom scPtr
>     schedContextZeroRefillMax scPtr
>     return (NullCap, NullCap)

Zombies have already been finalised.

> finaliseCap z@(Zombie {}) True _ =
>     return (z, NullCap)

Deletion of architecture-specific capabilities are handled in the architecture module.

> finaliseCap (ArchObjectCap { capCap = cap }) final _ =
>     Arch.finaliseCap cap final

When a final IRQ handler cap is finalised, the interrupt controller is notified. It will mask the IRQ, delete any internal references to the notification endpoint, and allow future "IRQControl" calls to create caps for this IRQ.

> finaliseCap cap@(IRQHandlerCap { capIRQ = irq }) True _ = do
>     deletingIRQHandler irq
>     return (NullCap, cap)

Zombie capabilities are always final.

> finaliseCap (Zombie {}) False _ = fail "Finalising a non-final zombie cap"

For any other capability, no special action is required.

> finaliseCap _ _ _ = return (NullCap, NullCap)

Some caps require deletion operations to occur after the slot has been emptied.

The deletion of the final IRQHandlerCap to any IRQ should be followed by
certain operations handled by deletedIRQHandler, including the clearing of
the bitmask bit that will allow the reissue of an IRQHandlerCap to this IRQ.

> postCapDeletion :: Capability -> Kernel ()
> postCapDeletion info = case info of
>     IRQHandlerCap irq -> deletedIRQHandler irq
>     ArchObjectCap c -> Arch.postCapDeletion c
>     _ -> return ()


> hasCancelSendRights :: Capability -> Bool
> hasCancelSendRights (EndpointCap { capEPCanSend = True,
>                                 capEPCanReceive = True,
>                                 capEPCanGrant = True,
>                                 capEPCanGrantReply  = True }) = True
> hasCancelSendRights _ = False

\subsection{Comparing Capabilities}

> sameRegionAs :: Capability -> Capability -> Bool

This function will return "True" if the left hand capability grants access to the physical resources that the right hand object grants access to. For example, if the left hand object is an untyped memory region, the result will be "True" for every capability with an object pointer inside that region. This is used by "sameObjectAs" and "isMDBParentOf".

This function assumes that its arguments are in MDB order.

> sameRegionAs a@(UntypedCap {}) b =
>     isPhysicalCap b && (baseA <= baseB) && (topB <= topA) && (baseB <= topB)
>     where
>         baseA = capPtr a
>         topA = baseA + PPtr (bit $ capBlockSize a) - 1
>         baseB = capUntypedPtr b
>         topB = baseB + PPtr (capUntypedSize b) - 1

> sameRegionAs (a@EndpointCap {}) (b@EndpointCap {}) =
>     capEPPtr a == capEPPtr b

> sameRegionAs (a@NotificationCap {}) (b@NotificationCap {}) =
>     capNtfnPtr a == capNtfnPtr b

> sameRegionAs (a@CNodeCap {}) (b@CNodeCap {}) =
>     capCNodePtr a == capCNodePtr b && capCNodeBits a == capCNodeBits b

> sameRegionAs (a@ThreadCap {}) (b@ThreadCap {}) =
>     capTCBPtr a == capTCBPtr b

> sameRegionAs (a@SchedContextCap {}) (b@SchedContextCap {}) =
>     capSchedContextPtr a == capSchedContextPtr b &&
>     capSCSize a == capSCSize b

> sameRegionAs SchedControlCap SchedControlCap = True

> sameRegionAs (a@ReplyCap {}) (b@ReplyCap {}) =
>     capReplyPtr a == capReplyPtr b

> sameRegionAs DomainCap     DomainCap     = True

> sameRegionAs IRQControlCap IRQControlCap = True
> sameRegionAs IRQControlCap (IRQHandlerCap {}) = True

> sameRegionAs (IRQHandlerCap a) (IRQHandlerCap b) = a == b

> sameRegionAs (ArchObjectCap a) (ArchObjectCap b) =
>     a `Arch.sameRegionAs` b

> sameRegionAs _ _ = False

> isPhysicalCap :: Capability -> Bool

This helper function to "sameRegionAs" checks that we have a physical capability, one which is generateable from an Untyped capability. Capabilities which refer to no particular kernel object, such as the IRQControl capability, and Reply capabilities generated by IPC, should never be compared to Untyped capabilities.

> isPhysicalCap NullCap = False
> isPhysicalCap IRQControlCap = False
> isPhysicalCap DomainCap = False
> isPhysicalCap (IRQHandlerCap {}) = False
> isPhysicalCap SchedControlCap = False
> isPhysicalCap (ArchObjectCap a) = Arch.isPhysicalCap a
> isPhysicalCap _ = True

> sameObjectAs :: Capability -> Capability -> Bool

If this function returns true, neither of the two arguments is a final typed capability for the purposes of "finaliseCap". Like "sameRegionAs", it assumes that its arguments are in MDB order.

The rules for determining this are generally the same as for "sameRegionAs". However, an untyped capability for an enclosing region on the left hand side does not prevent the right hand side capability being final. Likewise, an IRQ control capability on the left hand side does not prevent a IRQ handler capability being final.

> sameObjectAs (UntypedCap {}) _ = False
> sameObjectAs IRQControlCap (IRQHandlerCap {}) = False
> sameObjectAs (ArchObjectCap a) (ArchObjectCap b) = a `Arch.sameObjectAs` b
> sameObjectAs a b = a `sameRegionAs` b

\subsection{Modifying Capabilities}

The "updateCapData" function is used to update a capability when moving or copying it, given a data word provided by the user. It may return "NullCap" (given a valid input cap) if the user provides an invalid data word. The meaning of the data word depends on the type of the capability; some types do not use it at all.

The boolean argument is true when the capability is being updated by a "Mutate" or "Rotate" operation. In this case, any changes to the capability should not affect its MDB parent / child relationships; for example, endpoint capabilities may not have their badges changed.

> updateCapData :: Bool -> Word -> Capability -> Capability

Endpoint badges can never be changed once a nonzero badge is set; if the existing badge is not zero (the default value), then the update will fail.

> updateCapData preserve new cap@(EndpointCap {})
>     | not preserve && capEPBadge cap == 0 = cap { capEPBadge = new .&. mask badgeBits }
>     | otherwise = NullCap

> updateCapData preserve new cap@(NotificationCap {})
>     | not preserve && capNtfnBadge cap == 0 = cap { capNtfnBadge = new .&. mask badgeBits }
>     | otherwise = NullCap

The total of the guard size and the radix of the node cannot exceed the number of bits to be resolved in the entire address space. This prevents an overflow in the encoding used for CNode capabilities in the ARM implementation. Note that a CNode capability violating this restriction could never be used to look up a capability, so nothing is lost by enforcing it on all platforms.

> updateCapData _ w cap@(CNodeCap {})
>     | guardSize + capCNodeBits cap > finiteBitSize w = NullCap
>     | otherwise = cap {
>         capCNodeGuard = guard,
>         capCNodeGuardSize = guardSize }
>     where
>         guard = (w `shiftR` (Arch.cteRightsBits + guardSizeBits)) .&.
>             mask Arch.cteGuardBits .&. mask guardSize
>         guardSize = fromIntegral $ (w `shiftR` Arch.cteRightsBits) .&.
>             mask guardSizeBits
>         guardSizeBits = wordSizeCase 5 6

> updateCapData p w (ArchObjectCap { capCap = aoCap }) =
>     Arch.updateCapData p w aoCap
> updateCapData _ _ cap = cap

For 32-bit platforms, the C implementation only has space for 28 bits in the badge field. 64-bit platforms can use a full word.

> badgeBits :: Int
> badgeBits = wordSizeCase 28 64

The "maskCapRights" function restricts the operations that can be performed on a capability, given a set of rights.

> maskCapRights :: CapRights -> Capability -> Capability

> maskCapRights _ NullCap = NullCap
> maskCapRights _ DomainCap = DomainCap

> maskCapRights _ c@(UntypedCap {}) = c

> maskCapRights r c@(EndpointCap {}) = c {
>     capEPCanSend = capEPCanSend c && capAllowWrite r,
>     capEPCanReceive = capEPCanReceive c && capAllowRead r,
>     capEPCanGrant = capEPCanGrant c && capAllowGrant r,
>     capEPCanGrantReply = capEPCanGrantReply c && capAllowGrantReply r }

> maskCapRights r c@(NotificationCap {}) = c {
>     capNtfnCanSend = capNtfnCanSend c && capAllowWrite r,
>     capNtfnCanReceive = capNtfnCanReceive c && capAllowRead r }

> maskCapRights r c@(ReplyCap {}) = c{
>     capReplyCanGrant = capReplyCanGrant c && capAllowGrant r }

> maskCapRights _ c@(CNodeCap {}) = c

> maskCapRights _ c@(ThreadCap {}) = c

> maskCapRights _ c@IRQControlCap = c

> maskCapRights _ c@(IRQHandlerCap {}) = c

> maskCapRights _ c@(SchedContextCap {}) = c

> maskCapRights _ c@SchedControlCap = c

> maskCapRights r (ArchObjectCap {capCap = aoCap}) = Arch.maskCapRights r aoCap

> maskCapRights _ c@(Zombie {}) = c

\subsection{Creating and Deleting Objects}

The "createObject" function creates a new object in physical memory, and
returns the capabilities referring to it. Its parameters are an object
type; the base address of the destination memory region; and the object
size requested by the user. The latter is used only for variable-sized
objects such as frames or CNodes.

New threads are placed in the current security domain, which must be the domain of the creating thread.

> createObject :: ObjectType -> PPtr () -> Int -> Bool -> Kernel Capability
> createObject t regionBase userSize isDevice =
>     let funupd = (\f x v y -> if y == x then v else f y) in
>     case toAPIType t of
>         Just TCBObject -> do
>             curdom <- curDomain
>             placeNewObject regionBase ((makeObject :: TCB){tcbDomain = curdom}) 0
>             return $ ThreadCap (PPtr $ fromPPtr regionBase)
>         Just EndpointObject -> do
>             placeNewObject regionBase (makeObject :: Endpoint) 0
>             return $ EndpointCap (PPtr $ fromPPtr regionBase) 0 True True True True
>         Just NotificationObject -> do
>             placeNewObject (PPtr $ fromPPtr regionBase) (makeObject :: Notification) 0
>             return $ NotificationCap (PPtr $ fromPPtr regionBase) 0 True True
>         Just SchedContextObject -> do
>             let scp = PPtr $ fromPPtr regionBase
>             let newCap = SchedContextCap scp userSize
>             placeNewObject regionBase ((makeObject :: SchedContext){scRefills = replicate (refillAbsoluteMax newCap) emptyRefill}) 0
>             return $ newCap
>         Just ReplyObject -> do
>             placeNewObject regionBase (makeObject :: Reply) 0
>             return $ ReplyCap (PPtr $ fromPPtr regionBase) True
>         Just CapTableObject -> do
>             placeNewObject (PPtr $ fromPPtr regionBase) (makeObject :: CTE) userSize
>             modify (\ks -> ks { gsCNodes =
>               funupd (gsCNodes ks) (fromPPtr regionBase) (Just userSize)})
>             return $ CNodeCap (PPtr $ fromPPtr regionBase) userSize 0 0
>         Just Untyped ->
>             return $ UntypedCap isDevice (PPtr $ fromPPtr regionBase) userSize 0
>         Nothing -> do
>             archCap <- Arch.createObject t regionBase userSize isDevice
>             return $ ArchObjectCap archCap

\subsection{Invoking Objects}

The following functions are used to handle messages that are sent to kernel objects by user level code using a "Send" or "SendRecv" system call.

The "decodeInvocation" function parses the message, determines the operation that is being performed, and checks for any error conditions. If it returns successfully, the invocation is guaranteed to complete without any errors.

> decodeInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
>         Capability -> [(Capability, PPtr CTE)] -> Bool -> Maybe (PPtr Word) ->
>         KernelF SyscallError Invocation
>
> decodeInvocation _ _ _ _ cap@(EndpointCap {capEPCanSend=True}) _ _ _ = do
>     return $ InvokeEndpoint
>         (capEPPtr cap) (capEPBadge cap) (capEPCanGrant cap) (capEPCanGrantReply cap)
>
> decodeInvocation _ _ _ _ cap@(NotificationCap {capNtfnCanSend=True}) _ _ _ = do
>     return $ InvokeNotification (capNtfnPtr cap) (capNtfnBadge cap)
>
> decodeInvocation _ _ _ _ cap@(ReplyCap {}) _ _ _ = do
>     return $ InvokeReply (capReplyPtr cap) (capReplyCanGrant cap)
>
> decodeInvocation
>         label args _ slot cap@(ThreadCap {}) extraCaps False _ =
>     liftM InvokeTCB $ decodeTCBInvocation label args cap slot extraCaps
>
> decodeInvocation label args _ _ DomainCap extraCaps False _ =
>     liftM (uncurry InvokeDomain) $ decodeDomainInvocation label args extraCaps
>
> decodeInvocation label args _ _ (SchedContextCap {capSchedContextPtr=sc}) extraCaps False buffer =
>     liftM InvokeSchedContext $ decodeSchedContextInvocation label sc (map fst extraCaps) buffer
>
> decodeInvocation label args _ _ SchedControlCap extraCaps False _ =
>     liftM InvokeSchedControl $ decodeSchedControlInvocation label args (map fst extraCaps)
>
> decodeInvocation label args _ _ cap@(CNodeCap {}) extraCaps False _ =
>     liftM InvokeCNode $
>         decodeCNodeInvocation label args cap $ map fst extraCaps
>
> decodeInvocation label args _ slot cap@(UntypedCap {}) extraCaps _ _ =
>     liftM InvokeUntyped $
>         decodeUntypedInvocation label args slot cap $ map fst extraCaps
>
> decodeInvocation label args _ slot IRQControlCap extraCaps _ _ =
>     liftM InvokeIRQControl $
>         decodeIRQControlInvocation label args slot $ map fst extraCaps
>
> decodeInvocation label _ _ _ (IRQHandlerCap { capIRQ = irq }) extraCaps _ _ =
>     liftM InvokeIRQHandler $
>         decodeIRQHandlerInvocation label irq extraCaps
>
> decodeInvocation label args capIndex slot (ArchObjectCap cap) extraCaps _ _ =
>     liftM InvokeArchObject $
>         Arch.decodeInvocation label args capIndex slot cap extraCaps

If the capability cannot be invoked, because it is null or does not have a required right, then the operation returns "InvalidCapability".

> decodeInvocation _ _ _ _ _ _ _ _ = throw $ InvalidCapability 0

The "invoke" function performs the operation itself. It cannot throw faults, but it may be pre-empted. If it returns a list of words, they will be sent as a reply message with label 0; this is optional because the kernel does not generate replies from endpoint invocations.

This function just dispatches invocations to the type-specific invocation functions.

> performInvocation :: Bool -> Bool -> Bool -> Invocation -> KernelP [Word]
>
> performInvocation _ _ _ (InvokeUntyped invok) = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     invokeUntyped invok
>     return $ []
>
> performInvocation block call canDonate (InvokeEndpoint ep badge canGrant canGrantReply) =
>   withoutPreemption $ do
>     thread <- getCurThread
>     sendIPC block call badge canGrant canGrantReply canDonate thread ep
>     return $ []
>
> performInvocation _ _ _ (InvokeNotification ep badge) = do
>     withoutPreemption $ sendSignal ep badge
>     return $ []
>
> performInvocation _ _ _ (InvokeReply reply canGrantReply) =
>   withoutPreemption $ do
>     thread <- getCurThread
>     doReplyTransfer thread reply canGrantReply
>     return $ []
>
> performInvocation _ _ _ (InvokeTCB invok) = invokeTCB invok
>
> performInvocation _ _ _ (InvokeDomain thread domain) = withoutPreemption $ do
>     setDomain thread domain
>     return $ []
>
> performInvocation _ _ _ (InvokeCNode invok) = do
>     stateAssert sym_refs_asrt
>         "Assert that `sym_refs (state_refs_of' s)` holds"
>     invokeCNode invok
>     return $ []
>
> performInvocation _ _ _ (InvokeIRQControl invok) = do
>     performIRQControl invok
>     return $ []
>
> performInvocation _ _ _ (InvokeIRQHandler invok) = do
>     withoutPreemption $ invokeIRQHandler invok
>     return $ []
>
> performInvocation _ _ _ (InvokeSchedContext invok) = do
>     withoutPreemption $ invokeSchedContext invok
>     return $ []
>
> performInvocation _ _ _ (InvokeSchedControl invok) = do
>     withoutPreemption $ invokeSchedControlConfigureFlags invok
>     return $ []
>
> performInvocation _ _ _ (InvokeArchObject invok) = Arch.performInvocation invok

\subsection{Helper Functions}

The following two functions returns the base and size of the object a capability points to. They are used to determine whether the object is enclosed by an untyped capability, and are therefore undefined for capability types that cannot be MDB children of untyped capabilities.

> capUntypedPtr :: Capability -> PPtr ()
> capUntypedPtr NullCap = error "No valid pointer"
> capUntypedPtr (UntypedCap { capPtr = p }) = p
> capUntypedPtr (EndpointCap { capEPPtr = PPtr p }) = PPtr p
> capUntypedPtr (NotificationCap { capNtfnPtr = PPtr p }) = PPtr p
> capUntypedPtr (ReplyCap { capReplyPtr = PPtr p }) = PPtr p
> capUntypedPtr (CNodeCap { capCNodePtr = PPtr p }) = PPtr p
> capUntypedPtr (ThreadCap { capTCBPtr = PPtr p }) = PPtr p
> capUntypedPtr (SchedContextCap { capSchedContextPtr = PPtr p }) = PPtr p
> capUntypedPtr SchedControlCap = error "Schedule control has no pointer"
> capUntypedPtr DomainCap = error "Domain control has no pointer"
> capUntypedPtr (Zombie { capZombiePtr = PPtr p }) = PPtr p
> capUntypedPtr IRQControlCap = error "IRQ control has no pointer"
> capUntypedPtr (IRQHandlerCap {}) = error "IRQ handler has no pointer"
> capUntypedPtr (ArchObjectCap a) = Arch.capUntypedPtr a

> capUntypedSize :: Capability -> Word
> capUntypedSize NullCap = 0 -- was error in haskell
> capUntypedSize (UntypedCap { capBlockSize = b }) = 1 `shiftL` b
> capUntypedSize (CNodeCap { capCNodeBits = c })
>     = 1 `shiftL` (objBits (undefined::CTE) + c)
> capUntypedSize (EndpointCap {})
>     = 1 `shiftL` objBits (undefined::Endpoint)
> capUntypedSize (NotificationCap {})
>     = 1 `shiftL` objBits (undefined::Notification)
> capUntypedSize (ThreadCap {})
>     = 1 `shiftL` objBits (undefined::TCB)
> capUntypedSize (SchedContextCap { capSCSize = b })
>     = 1 `shiftL` b
> capUntypedSize SchedControlCap = 1 -- error in haskell
> capUntypedSize (DomainCap {})
>     = 1 -- error in haskell
> capUntypedSize (ArchObjectCap a)
>     = Arch.capUntypedSize a
> capUntypedSize (Zombie { capZombieType = ZombieTCB })
>     = 1 `shiftL` objBits (undefined::TCB)
> capUntypedSize (Zombie { capZombieType = ZombieCNode sz })
>     = 1 `shiftL` (objBits (undefined::CTE) + sz)
> capUntypedSize (ReplyCap {})
>     = 1 `shiftL` objBits (undefined::Reply)
> capUntypedSize (IRQControlCap {})
>     = 1 -- error in haskell
> capUntypedSize (IRQHandlerCap {})
>     = 1 -- error in haskell

> replyClear :: PPtr Reply -> PPtr TCB -> Kernel ()
> replyClear rptr tptr = do
>     state <- getThreadState $ tptr
>     case state of
>         BlockedOnReply _ -> replyRemove rptr tptr
>         BlockedOnReceive {} -> cancelIPC tptr
>         _ -> fail "replyClear: invalid state of replyTCB"
