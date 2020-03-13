%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

\begin{impdetails}

> {-# LANGUAGE CPP, EmptyDataDecls, GeneralizedNewtypeDeriving #-}

\end{impdetails}

This module defines instances of "PSpaceStorable" for ARM-specific kernel objects. This includes page table and page directory entries, and ASID pools.

> module SEL4.Object.Instances.ARM where

\begin{impdetails}

> import SEL4.Machine.Hardware.ARM(PTE(..), PDE(..))
> import SEL4.Object.Structures
> import SEL4.Model
> import Data.Helpers
#ifdef CONFIG_ARM_SMMU
> import SEL4.Machine.Hardware.ARM(IOPTE(..), IOPDE(..))
#endif

\end{impdetails}

> instance PSpaceStorable PDE where
>     makeObject = InvalidPDE
>     injectKO = KOArch . KOPDE
>     projectKO o = case o of
>                   KOArch (KOPDE p) -> return p
>                   _ -> typeError "PDE" o

> instance PSpaceStorable PTE where
>     makeObject = InvalidPTE
>     injectKO = KOArch . KOPTE
>     projectKO o = case o of
>                 KOArch (KOPTE p) -> return p
>                 _ -> typeError "PTE" o

#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> instance PSpaceStorable VCPU where
>     makeObject = makeVCPUObject
>     injectKO = KOArch . KOVCPU
>     projectKO o = case o of
>                 KOArch (KOVCPU p) -> return p
>                 _ -> typeError "VCPU" o
#endif

#ifdef CONFIG_ARM_SMMU
> instance PSpaceStorable IOPDE where
>     makeObject = InvalidIOPDE
>     injectKO = KOArch . KOIOPDE
>     projectKO o = case o of
>                   KOArch (KOIOPDE p) -> return p
>                   _ -> typeError "IOPDE" o

> instance PSpaceStorable IOPTE where
>     makeObject = InvalidIOPTE
>     injectKO = KOArch . KOIOPTE
>     projectKO o = case o of
>                 KOArch (KOIOPTE p) -> return p
>                 _ -> typeError "IOPTE" o
#endif

> instance PSpaceStorable ASIDPool where
>     makeObject = ASIDPool $
>         funPartialArray (const Nothing) (0,1023)
>     injectKO = KOArch . KOASIDPool
>     projectKO o = case o of
>         KOArch (KOASIDPool e) -> return e
>         _ -> typeError "ASID pool" o

