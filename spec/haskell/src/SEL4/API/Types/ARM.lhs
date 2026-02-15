%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains an instance of the machine-specific kernel API for the ARM architecture with hypervisor extensions.

> {-# LANGUAGE CPP #-}

> module SEL4.API.Types.ARM where

> import SEL4.API.Types.Universal(APIObjectType(..),
>                                 epSizeBits, ntfnSizeBits, cteSizeBits)
> import SEL4.Machine.Hardware.ARM
> import Data.List (elemIndex)
> import Data.Maybe (fromJust)
> import Data.WordLib (wordSizeCase)

There are three ARM-specific object types: virtual pages, page tables, and page directories.

Hypervisor additions add VCPUs.

I/O MMU additions add IO page table objects. Note that there is only one IO page directory created at kernel boot, which cannot be created or deleted. Hence IO page directories are not considered kernel objects.

> data ObjectType
>     = APIObjectType APIObjectType
>     | SmallPageObject
>     | LargePageObject
>     | SectionObject
>     | SuperSectionObject
>     | PageTableObject
>     | PageDirectoryObject
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>     | VCPUObject
#endif
#ifdef CONFIG_ARM_SMMU
>     | IOPageTableObject
#endif
>     deriving (Show, Eq)

> instance Bounded ObjectType where
>     minBound = APIObjectType minBound
>     maxBound = PageDirectoryObject

> instance Enum ObjectType where
>     fromEnum e =
>         -- This definition is ignored in Isabelle, the order is defined in the
>         -- skeleton file instead.
>         let apiMax = fromEnum (maxBound :: APIObjectType)
>         in case e of
>             APIObjectType a -> fromEnum a
>             SmallPageObject -> apiMax + 1
>             LargePageObject -> apiMax + 2
>             SectionObject -> apiMax + 3
>             SuperSectionObject -> apiMax + 4
>             PageTableObject -> apiMax + 5
>             PageDirectoryObject -> apiMax + 6
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>             VCPUObject -> apiMax + 7
#endif
#ifdef CONFIG_ARM_SMMU
>             IOPageTableObject -> apiMax + 8
#endif
>     toEnum n
>         | n <= apiMax = APIObjectType $ toEnum n
>         | n == fromEnum SmallPageObject = SmallPageObject
>         | n == fromEnum LargePageObject = LargePageObject
>         | n == fromEnum SectionObject = SectionObject
>         | n == fromEnum SuperSectionObject = SuperSectionObject
>         | n == fromEnum PageTableObject = PageTableObject
>         | n == fromEnum PageDirectoryObject = PageDirectoryObject
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>         | n == fromEnum VCPUObject = VCPUObject
#endif
#ifdef CONFIG_ARM_SMMU
>         | n == fromEnum IOPageTableObject = IOPageTableObject
#endif
>         | otherwise = error "toEnum out of range for ARM.ObjectType"
>         where apiMax = fromEnum (maxBound :: APIObjectType)

> fromAPIType = APIObjectType

> toAPIType (APIObjectType a) = Just a
> toAPIType _ = Nothing

> pageType = SmallPageObject

> tcbBlockSizeBits :: Int
> tcbBlockSizeBits = 9

> apiGetObjectSize :: APIObjectType -> Int -> Int
> apiGetObjectSize Untyped size = size
> apiGetObjectSize TCBObject _ = tcbBlockSizeBits
> apiGetObjectSize EndpointObject _ = epSizeBits
> apiGetObjectSize NotificationObject _ = ntfnSizeBits
> apiGetObjectSize CapTableObject size = cteSizeBits + size

> getObjectSize :: ObjectType -> Int -> Int
> getObjectSize SmallPageObject _ = pageBitsForSize ARMSmallPage
> getObjectSize LargePageObject _ = pageBitsForSize ARMLargePage
> getObjectSize SectionObject _ = pageBitsForSize ARMSection
> getObjectSize SuperSectionObject _ = pageBitsForSize ARMSuperSection
> getObjectSize PageTableObject _ = ptBits
> getObjectSize PageDirectoryObject _ = pdBits
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
> getObjectSize VCPUObject _ = vcpuBits
#endif
#ifdef CONFIG_ARM_SMMU
> getObjectSize IOPageTableObject _ = ioptBits
#endif
> getObjectSize (APIObjectType apiObjectType) size = apiGetObjectSize apiObjectType size


> isFrameType :: ObjectType -> Bool
> isFrameType SmallPageObject = True
> isFrameType LargePageObject = True
> isFrameType SectionObject = True
> isFrameType SuperSectionObject = True
> isFrameType _ = False

