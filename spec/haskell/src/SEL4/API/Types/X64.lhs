%
% Copyright 2014, General Dynamics C4 Systems
%
% SPDX-License-Identifier: GPL-2.0-only
%

This module contains an instance of the machine-specific kernel API for the x64 architecture.

> module SEL4.API.Types.X64 where

> import SEL4.API.Types.Universal(APIObjectType(..),
>                                 epSizeBits, ntfnSizeBits, cteSizeBits)
> import SEL4.Machine.Hardware.X64
> import Data.WordLib(wordSizeCase)

There are seven x86 64bit-specific object types:
pages of 3 sizes, and 4 levels of page tables.

> data ObjectType
>     = APIObjectType APIObjectType
>     | SmallPageObject
>     | LargePageObject
>     | HugePageObject
>     | PageTableObject
>     | PageDirectoryObject
>     | PDPointerTableObject
>     | PML4Object
>     deriving (Show, Eq)

> instance Bounded ObjectType where
>     minBound = APIObjectType minBound
>     maxBound = PML4Object

> instance Enum ObjectType where
>     fromEnum e = case e of
>         APIObjectType a -> fromEnum a
>         SmallPageObject -> apiMax + 1
>         LargePageObject -> apiMax + 2
>         HugePageObject -> apiMax + 3
>         PageTableObject -> apiMax + 4
>         PageDirectoryObject -> apiMax + 5
>         PDPointerTableObject -> apiMax + 6
>         PML4Object -> apiMax + 7
>         where apiMax = fromEnum (maxBound :: APIObjectType)
>     toEnum n
>         | n <= apiMax = APIObjectType $ toEnum n
>         | n == apiMax + 1 = SmallPageObject
>         | n == apiMax + 2 = LargePageObject
>         | n == apiMax + 3 = HugePageObject
>         | n == apiMax + 4 = PageTableObject
>         | n == apiMax + 5 = PageDirectoryObject
>         | n == apiMax + 6 = PDPointerTableObject
>         | n == apiMax + 7 = PML4Object
>         | otherwise = error "toEnum out of range for X64.ObjectType"
>         where apiMax = fromEnum (maxBound :: APIObjectType)

> fromAPIType = APIObjectType

> toAPIType (APIObjectType a) = Just a
> toAPIType _ = Nothing

> pageType = SmallPageObject

> tcbBlockSizeBits :: Int
> tcbBlockSizeBits = 11

> apiGetObjectSize :: APIObjectType -> Int -> Int
> apiGetObjectSize Untyped size = size
> apiGetObjectSize TCBObject _ = tcbBlockSizeBits
> apiGetObjectSize EndpointObject _ = epSizeBits
> apiGetObjectSize NotificationObject _ = ntfnSizeBits
> apiGetObjectSize CapTableObject size = cteSizeBits + size

> getObjectSize :: ObjectType -> Int -> Int
> getObjectSize SmallPageObject _ = pageBitsForSize X64SmallPage
> getObjectSize LargePageObject _ = pageBitsForSize X64LargePage
> getObjectSize HugePageObject _ = pageBitsForSize X64HugePage
> getObjectSize PageTableObject _ = ptBits
> getObjectSize PageDirectoryObject _ = ptBits
> getObjectSize PDPointerTableObject _ = ptBits
> getObjectSize PML4Object _ = ptBits
> getObjectSize (APIObjectType apiObjectType) size = apiGetObjectSize apiObjectType size


> isFrameType :: ObjectType -> Bool
> isFrameType SmallPageObject = True
> isFrameType LargePageObject = True
> isFrameType HugePageObject = True
> isFrameType _ = False

