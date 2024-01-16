%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module defines the behavior of untyped objects.

> module SEL4.Object.Untyped (
>         decodeUntypedInvocation, invokeUntyped
>     ) where

\begin{impdetails}

> import Prelude hiding (Word)
> import SEL4.Config
> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.API.Invocation
> import SEL4.API.InvocationLabels
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object.Structures
> import SEL4.Object.Instances()
> import {-# SOURCE #-} SEL4.Object.CNode
> import {-# SOURCE #-} SEL4.Kernel.CSpace

> import Data.Bits
> import Data.WordLib

\end{impdetails}

\subsection{Invocation}

Invocation of an untyped object retypes the memory region, possibly creating
new typed kernel objects. As shown in \autoref{fig:derive}, the
retype operation will generate one or more new capabilities, which are inserted in the mapping database as children of the initial capability. These newly created capabilities will have all access rights, and other object specific fields will be initialised to some sensible value.

\begin{figure}[htp]
\centering \includegraphics{figures/derive}
\caption{Invoking an Untyped Object}\label{fig:derive}
\end{figure}

We start by defining a simple function to align one value to a power-of-two boundary. In particular, this function aligns its first argument up to the next power-of-two specified by the second argument.

> alignUp :: Word -> Int -> Word
> alignUp baseValue alignment =
>   (baseValue + (1 `shiftL` alignment) - 1) .&. complement (mask alignment)

The expected parameters are the type of the new objects, the size of the requested objects (for those with variable size), a capability to a capability space, index and depth used to locate the destination for the new capabilities, and the maximum number of new capabilities to be created. When successful, it returns the number of new objects or regions created.

> decodeUntypedInvocation :: Word -> [Word] -> PPtr CTE -> Capability ->
>         [Capability] -> KernelF SyscallError UntypedInvocation
> decodeUntypedInvocation label
>         (newTypeW:userObjSizeW:nodeIndexW:nodeDepthW:nodeOffset:nodeWindow:_)
>         slot cap (rootCap:_) =
>   do

The only supported operation on Untyped capabilities is Retype.

>     unless (genInvocationType label == UntypedRetype) $ throw IllegalOperation

The first argument must be a valid object type.

>     when (fromIntegral newTypeW > fromEnum (maxBound :: ObjectType)) $
>         throw $ InvalidArgument 0
>     let newType = toEnum (fromIntegral newTypeW) :: ObjectType

The second argument specifies the size of the object, for the types for which the object size may vary --- untyped memory, data frames, and CNodes, and possibly architecture-defined types. For any other type, it is not used. It must be a positive integer less than the number of bits in a physical address.

The value of this argument is the base 2 logarithm of the actual required size. The unit depends on the object type: one byte for untyped memory objects, the architecture's minimum page size for data frames, and one capability slot for CNodes.

>     let userObjSize = fromIntegral userObjSizeW
>     let objectSize = getObjectSize newType userObjSize

The retype fails if the requested object size is too large.

>     unless (userObjSize < wordBits) $
>         throw $ RangeError 0 $ fromIntegral maxUntypedSizeBits
>     rangeCheck objectSize 0 maxUntypedSizeBits

The kernel does not allow creation of CNodes containing only one entry; this is done to avoid non-terminating loops in capability lookup. Note that it is possible for a single entry CNode to translate bits using its guard; this is not allowed, however, to avoid having to check for it during capability lookups.

>     when (newType == fromAPIType CapTableObject && userObjSize == 0) $
>         throw $ InvalidArgument 1

Because of capability size limitations, the kernel does not allow creation of objects smaller than 16 bytes.

>     when (newType == fromAPIType Untyped && userObjSize < minUntypedSizeBits) $
>         throw $ InvalidArgument 1

The node index and depth arguments, and the root capability, specify a CNode to place newly created capabilities in. This is similar to the source argument of the Insert and Move operations. However, unlike those operations, the specified slot must contain a CNode capability, and the new capabilities will be placed in \emph{that} CNode. % XXX should have either a diagram, or a more intuitive way to specify the destination.

>     let nodeIndex = CPtr nodeIndexW
>     let nodeDepth = fromIntegral nodeDepthW
>
>     nodeCap <- if nodeDepth == 0
>         then return rootCap
>         else do
>             nodeSlot <- lookupTargetSlot rootCap nodeIndex nodeDepth
>             withoutFailure $ getSlotCap nodeSlot

If the destination capability is not a CNode, an error is returned.

>     case nodeCap of
>         CNodeCap {} -> return ()
>         _ -> throw $ FailedLookup False $ MissingCapability {
>             missingCapBitsLeft = nodeDepth }

The node offset and window arguments specify the start and the length of a contiguous block of empty capability slots in the destination CNode.

>     let nodeSize = 1 `shiftL` (capCNodeBits nodeCap)
>     rangeCheck nodeOffset 0 $ nodeSize - 1
>     rangeCheck nodeWindow 1 retypeFanOutLimit
>     rangeCheck nodeWindow 1 $ nodeSize - nodeOffset
>
>     slots <- withoutFailure $
>         mapM (locateSlotCap nodeCap)
>             [nodeOffset .. nodeOffset+nodeWindow - 1]

The destination slots must all be empty. If any of them contains a capability, the operation will fail with a "DeleteFirst" error.

>     mapM_ ensureEmptySlot slots

If we discover we don't have any children (for instance, they have all been manually deleted), we reset the untyped region, clearing any memory that had been used.

>     reset <- withoutFailure $ constOnFailure False $ do
>             ensureNoChildren slot
>             return True

The memory free for use begins at the current free pointer, unless we are performing a reset, in which case it begins at the start of the region.

>     let freeIndex = if reset then 0 else capFreeIndex cap
>     let freeRef = getFreeRef (capPtr cap) freeIndex

Ensure that sufficient space is available in the region of memory.

>     let untypedFreeBytes = (bit (capBlockSize cap)) - freeIndex
>     let maxCount = untypedFreeBytes `shiftR` objectSize
>     when (fromIntegral maxCount < nodeWindow) $
>         throw $ NotEnoughMemory $ fromIntegral untypedFreeBytes

Check that if the user is trying to retype a device untyped cap, they are only creating
device frames, or other device untypeds

>     let notFrame = not $ isFrameType newType
>     let isDevice = capIsDevice cap
>     when (isDevice && notFrame && newType /= fromAPIType Untyped) $
>            throw $ InvalidArgument 1

Align up the free region pointer to ensure that created objects are aligned to their size.

>     let alignedFreeRef = PPtr $ alignUp (fromPPtr freeRef) objectSize

>     return $ Retype {
>         retypeSource = slot,
>         retypeResetUntyped = reset,
>         retypeRegionBase = capPtr cap,
>         retypeFreeRegionBase = alignedFreeRef,
>         retypeNewType = newType,
>         retypeNewSizeBits = userObjSize,
>         retypeSlots = slots,
>         retypeIsDevice = isDevice }

> decodeUntypedInvocation label _ _ _ _ = throw $
>     if genInvocationType label == UntypedRetype
>         then TruncatedMessage
>         else IllegalOperation

A Retype operation may begin with a reset of an Untyped cap. This returns the free space pointer to the start of the Untyped region. For large regions this is done preemptibly, one chunk at a time.

> resetUntypedCap :: PPtr CTE -> KernelP ()
> resetUntypedCap slot = do
>     cap <- withoutPreemption $ getSlotCap slot
>     let sz = capBlockSize cap
>     unless (capFreeIndex cap == 0) $ do

\begin{impdetails}
The objects in the Haskell model are removed at this time. This operation is specific to the Haskell physical memory model, in which memory objects are typed; it is not necessary (or possible) when running on real hardware.

>         withoutPreemption $ deleteObjects (capPtr cap) sz

\end{impdetails}

>         if (capIsDevice cap || sz < resetChunkBits)
>             then withoutPreemption $ do
>                 unless (capIsDevice cap) $ doMachineOp $
>                     clearMemory (PPtr (fromPPtr (capPtr cap))) (1 `shiftL` sz)
>                 updateFreeIndex slot 0
>             else forM_ (reverse [capPtr cap, capPtr cap + (1 `shiftL` resetChunkBits) ..
>                             getFreeRef (capPtr cap) (capFreeIndex cap) - 1])
>                 $ \addr -> do
>                     withoutPreemption $ doMachineOp $ clearMemory
>                         (PPtr (fromPPtr addr)) (1 `shiftL` resetChunkBits)
>                     withoutPreemption $ updateFreeIndex slot
>                         (getFreeIndex (capPtr cap) addr)
>                     preemptionPoint

\begin{impdetails}
Will be set to something stricter in Isabelle when required.

> canonicalAddressAssert :: PPtr () -> Bool
> canonicalAddressAssert p = True

\end{impdetails}

> invokeUntyped :: UntypedInvocation -> KernelP ()
> invokeUntyped (Retype srcSlot reset base retypeBase newType userSize destSlots isDev) = do

>     when reset $ resetUntypedCap srcSlot
>     withoutPreemption $ do

For verification purposes a check is made that the region the objects are created in does not overlap with any existing CNodes.

>         let totalObjectSize = (length destSlots) `shiftL` (getObjectSize newType userSize)
>         let inRange = (\x -> fromPPtr retypeBase <= x &&
>                              x <= fromPPtr retypeBase + fromIntegral totalObjectSize - 1)
>         stateAssert (\s -> not (cNodeOverlap (gsCNodes s) inRange))
>             "CNodes present in region to be retyped."
>         stateAssert (\s -> not (archOverlap s inRange))
>             "Arch specific non-overlap requirements."
>         assert (canonicalAddressAssert retypeBase) "Canonical ptr required on some architectures"
>         let freeRef = retypeBase + PPtr (fromIntegral totalObjectSize)
>         updateFreeIndex srcSlot (getFreeIndex base freeRef)

Create the new objects and insert caps to these objects into the destination slots.

>         createNewObjects newType srcSlot destSlots retypeBase userSize isDev

This function performs the check that CNodes do not overlap with the retyping region. Its actual definition is provided in the Isabelle translation.

> cNodeOverlap :: (Word -> Maybe Int) -> (Word -> Bool) -> Bool
> cNodeOverlap _ _ = False

Architecture specific assertion similar to cNodeOverlap, for architectures that have variable-sized objects.

> archOverlap :: KernelState -> (Word -> Bool) -> Bool
> archOverlap _ _ = False
