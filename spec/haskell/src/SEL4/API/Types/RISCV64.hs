-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)


-- This module contains an instance of the machine-specific kernel API for the
-- RISC-V architecture.

module SEL4.API.Types.RISCV64 where

import SEL4.API.Types.Universal(APIObjectType, apiGetObjectSize)
import SEL4.Machine.Hardware.RISCV64

-- There are two page sizes on RISCV, and one extra size specific to 64-bit.
-- We are keeping with the design spec naming convention here; in C they are
-- referred to as 4K, Mega and Giga Pages respectively.

data ObjectType
    = APIObjectType APIObjectType
    | SmallPageObject
    | LargePageObject
    | HugePageObject
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
