--
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--


-- This module contains an instance of the machine-specific kernel API for the
-- RISC-V architecture.

module SEL4.API.Types.RISCV64 where

import SEL4.API.Types.Universal(APIObjectType(..),
                                epSizeBits, ntfnSizeBits, cteSizeBits)
import SEL4.Machine.Hardware.RISCV64
import Data.WordLib(wordSizeCase)

-- There are two page sizes on RISCV, and one extra size specific to 64-bit.
-- We are keeping with the design spec naming convention here; in C they are
-- referred to as 4K, Mega and Giga Pages respectively.

data ObjectType
    = APIObjectType APIObjectType
    | HugePageObject
    | SmallPageObject
    | LargePageObject
    | PageTableObject
    deriving (Show, Eq)

instance Bounded ObjectType where
    minBound = APIObjectType minBound
    maxBound = PageTableObject

-- the order of these does not matter, any order that creates an enumeration
-- will suffice to derive Enum

instance Enum ObjectType where
    fromEnum e = case e of
        APIObjectType a -> fromEnum a
        SmallPageObject -> apiMax + 1
        LargePageObject -> apiMax + 2
        HugePageObject -> apiMax + 3
        PageTableObject -> apiMax + 4
        where apiMax = fromEnum (maxBound :: APIObjectType)
    toEnum n
        | n <= apiMax = APIObjectType $ toEnum n
        | n == apiMax + 1 = SmallPageObject
        | n == apiMax + 2 = LargePageObject
        | n == apiMax + 3 = HugePageObject
        | n == apiMax + 4 = PageTableObject
        | otherwise = error "toEnum out of range for RISCV.ObjectType"
        where apiMax = fromEnum (maxBound :: APIObjectType)

fromAPIType = APIObjectType

toAPIType (APIObjectType a) = Just a
toAPIType _ = Nothing

pageType = SmallPageObject

tcbBlockSizeBits :: Int
tcbBlockSizeBits = 10

apiGetObjectSize :: APIObjectType -> Int -> Int
apiGetObjectSize Untyped size = size
apiGetObjectSize TCBObject _ = tcbBlockSizeBits
apiGetObjectSize EndpointObject _ = epSizeBits
apiGetObjectSize NotificationObject _ = ntfnSizeBits
apiGetObjectSize CapTableObject size = cteSizeBits + size

getObjectSize :: ObjectType -> Int -> Int
getObjectSize PageTableObject _ = ptBits
getObjectSize SmallPageObject _ = pageBitsForSize RISCVSmallPage
getObjectSize LargePageObject _ = pageBitsForSize RISCVLargePage
getObjectSize HugePageObject _ = pageBitsForSize RISCVHugePage
getObjectSize (APIObjectType apiObjectType) size = apiGetObjectSize apiObjectType size

isFrameType :: ObjectType -> Bool
isFrameType SmallPageObject = True
isFrameType LargePageObject = True
isFrameType HugePageObject = True
isFrameType _ = False
