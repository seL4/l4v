%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module contains an instance of the machine-specific kernel API for the ARM architecture with hypervisor extensions.

> {-# LANGUAGE CPP #-}

> module SEL4.API.Types.ARM_HYP where

> import SEL4.API.Types.Universal(APIObjectType, apiGetObjectSize)
> import SEL4.Machine.Hardware.ARM_HYP
> import Data.List (elemIndex)
> import Data.Maybe (fromJust)

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
>       case e of
>           APIObjectType a -> fromEnum a
>           _ -> apiMax + 1 + archToIndex e
>           where apiMax = fromEnum (maxBound :: APIObjectType)
>                 archToIndex c = fromJust $ elemIndex c
>                     [SmallPageObject
>                     ,LargePageObject
>                     ,SectionObject
>                     ,SuperSectionObject
>                     ,PageTableObject
>                     ,PageDirectoryObject
#ifdef CONFIG_ARM_HYPERVISOR_SUPPORT
>                     ,VCPUObject
#endif
#ifdef CONFIG_ARM_SMMU
>                     ,IOPageTableObject
#endif
>                     ]
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

