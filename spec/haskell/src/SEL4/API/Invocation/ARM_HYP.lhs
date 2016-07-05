%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines the machine-specific invocations for the ARM.

\begin{impdetails}

This module makes use of the GHC extension allowing data types with no constructors.

> {-# LANGUAGE EmptyDataDecls, CPP #-}

\end{impdetails}

> module SEL4.API.Invocation.ARM_HYP where

\begin{impdetails}

> import SEL4.Machine
> import SEL4.Machine.Hardware.ARM_HYP hiding (PAddr)
> import SEL4.Object.Structures
> import SEL4.API.InvocationLabels
> import SEL4.API.InvocationLabels.ARM_HYP

> import Data.Word(Word8,Word16,Word32)

\end{impdetails}

\subsection{ARM-Specific Objects}

There are five ARM-specific object types; however, only four of them may be invoked. These are the page table, page, ASID control, and ASID pool objects.

IO pages are invoked using InvokePage (cap contains a bit indicating it is an IO page).

> data Invocation
>     = InvokePageTable PageTableInvocation
>     | InvokePageDirectory PageDirectoryInvocation
>     | InvokePage PageInvocation
>     | InvokeASIDControl ASIDControlInvocation
>     | InvokeASIDPool ASIDPoolInvocation
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     | InvokeVCPU VCPUInvocation
#endif
#ifdef CONFIG_ARM_SMMU
>     | InvokeIOSpace IOSpaceInvocation
>     | InvokeIOPageTable IOPageTableInvocation
#endif
>     deriving Show

> data PageTableInvocation
>     = PageTableUnmap {
>         ptUnmapCap :: ArchCapability,
>         ptUnmapCapSlot :: PPtr CTE }
>     | PageTableMap {
>         ptMapCap :: Capability,
>         ptMapCTSlot :: PPtr CTE,
>         ptMapPDE :: PDE,
>         ptMapPDSlot :: PPtr PDE }
>     deriving Show

> data PageDirectoryInvocation
>     = PageDirectoryNothing
>     | PageDirectoryFlush {
>         pdFlushType :: FlushType,
>         pdFlushStart :: VPtr,
>         pdFlushEnd :: VPtr,
>         pdFlushPStart :: PAddr,
>         pdFlushPD :: PPtr PDE,
>         pdFlushASID :: ASID }
>     deriving Show

> data PageInvocation
>     = PageGetAddr {
>         pageGetBasePtr :: PPtr Word }
>     | PageFlush {
>         pageFlushType :: FlushType,
>         pageFlushStart :: VPtr,
>         pageFlushEnd :: VPtr,
>         pageFlushPStart :: PAddr,
>         pageFlushPD :: PPtr PDE,
>         pageFlushASID :: ASID }
>     | PageRemap {
>         pageRemapASID :: ASID,
>         pageRemapEntries :: Either (PTE, [PPtr PTE]) (PDE, [PPtr PDE]) }
>     | PageMap {
>         pageMapASID :: ASID,
>         pageMapCap :: Capability,
>         pageMapCTSlot :: PPtr CTE,
>         pageMapEntries :: Either (PTE, [PPtr PTE]) (PDE, [PPtr PDE]) }
>     | PageUnmap {
>         pageUnmapCap :: ArchCapability,
>         pageUnmapCapSlot :: PPtr CTE }
>     deriving Show

> data FlushType
>     = Clean | Invalidate | CleanInvalidate | Unify
>     deriving Show

> data ASIDControlInvocation
>     = MakePool {
>         makePoolFrame :: PPtr (),
>         makePoolSlot :: PPtr CTE,
>         makePoolParent :: PPtr CTE,
>         makePoolBase :: ASID }
>     deriving Show

> data ASIDPoolInvocation
>     = Assign {
>         assignASID :: ASID,
>         assignASIDPool :: PPtr ASIDPool,
>         assignASIDCTSlot :: PPtr CTE }
>     deriving Show

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT

\subsection{VCPUs}

FIXME ARMHYP move HyperReg definition (to Hardware?)

> type HyperReg = Word32 -- FIXME ARMHYP can abstract
> type HyperRegVal = Word32 -- FIXME ARMHYP can abstract

> data VCPUInvocation
>     = VCPUSetTCB (PPtr VCPU) (PPtr TCB)
>     -- XXX ARMHYP vcpu index group priority virq
>     | VCPUInjectIRQ (PPtr VCPU) Word8 Word8 Word8 Word8 Word16
>     | VCPUReadRegister (PPtr VCPU) HyperReg
>     | VCPUWriteRegister (PPtr VCPU) HyperReg HyperRegVal
>     deriving (Show, Eq)

#endif

#ifdef CONFIG_ARM_SMMU

\subsection{IO Page Tables}

FIXME ARMHYP there is an assymetry here compared to how we deal with normal
pages: IOPageTableMap handles IOPDEs, PageMapIO handles IOPTEs, but on
the normal MMU side PageMap handles both

> data IOPageTableInvocation
>     = IOPageTableUnmap {
>         ioptUnmapCap :: ArchCapability,
>         ioptUnmapCapSlot :: PPtr CTE }
>     | IOPageTableMap {
>         ioptMapASID :: ASID,
>         ioptMapCap :: ArchCapability,
>         ioptMapSlot :: PPtr CTE,
>         ioptMapEntry :: (IOPDE, PPtr IOPDE),
>         ioptMapAddress :: PAddr}
>     deriving Show

> data PageInvocationIO
>     = PageMapIO {
>         pageMapIOASID :: ASID,
>         pageMapIOCap :: Capability,
>         pageMapIOCTSlot :: PPtr CTE,
>         pageMapIOEntry :: IOPTE,
>         pageMapIOAddress :: PAddr}
>     deriving Show

\subsection{IO Spaces}

The ARM platform presently does not support an IO space invocations.

> data IOSpaceInvocation = ARMNoArchIOSpace
>     deriving Show

#endif

\subsection{Interrupt Control}

The ARM platform presently does not require any additional interrupt control calls.

> data IRQControlInvocation = ARMNoArchIRQControl
>     deriving Show

\subsection{Additional Register Subsets}

The ARM platform currently does not define any additional register sets for the "CopyRegisters" operation. This may be changed in future to support a floating point unit.

> data CopyRegisterSets = ARMNoExtraRegisters
>     deriving Show

> isPDFlushLabel :: InvocationLabel -> Bool
> isPDFlushLabel x = case x of
>       ArchInvocationLabel ARMPDClean_Data -> True
>       ArchInvocationLabel ARMPDInvalidate_Data -> True
>       ArchInvocationLabel ARMPDCleanInvalidate_Data -> True
>       ArchInvocationLabel ARMPDUnify_Instruction -> True
>       _ -> False

> isPageFlushLabel :: InvocationLabel -> Bool
> isPageFlushLabel x = case x of
>       ArchInvocationLabel ARMPageClean_Data -> True
>       ArchInvocationLabel ARMPageInvalidate_Data -> True
>       ArchInvocationLabel ARMPageCleanInvalidate_Data -> True
>       ArchInvocationLabel ARMPageUnify_Instruction -> True
>       _ -> False

