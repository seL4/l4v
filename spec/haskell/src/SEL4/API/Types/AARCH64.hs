--
-- Copyright 2022, Proofcraft Pty Ltd
-- Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains an instance of the machine-specific kernel API for the
-- AArch64 architecture.

module SEL4.API.Types.AARCH64 where

import SEL4.API.Types.Universal(APIObjectType(..),
                                epSizeBits, ntfnSizeBits, cteSizeBits)
import SEL4.Machine.Hardware.AARCH64
import Data.WordLib(wordSizeCase)

-- There are three page sizes on AArch64 plus two page table sizes in hyp mode
-- (top-level and non-top-level). Hypervisor additions add VCPUs.

data ObjectType
    = APIObjectType APIObjectType
    | HugePageObject
    | VSpaceObject
    | SmallPageObject
    | LargePageObject
    | PageTableObject
    | VCPUObject
    deriving (Show, Eq)

instance Bounded ObjectType where
    minBound = APIObjectType minBound
    maxBound = VCPUObject

-- the order of these does not matter, any order that creates an enumeration
-- will suffice to derive Enum. The actual order is defined in the corresponding
-- design/skel file. We mirror this order here purely for consistency.

instance Enum ObjectType where
    fromEnum e = case e of
        APIObjectType a -> fromEnum a
        HugePageObject -> apiMax + 1
        VSpaceObject -> apiMax + 2
        SmallPageObject -> apiMax + 3
        LargePageObject -> apiMax + 4
        PageTableObject -> apiMax + 5
        VCPUObject -> apiMax + 6
        where apiMax = fromEnum (maxBound :: APIObjectType)
    toEnum n
        | n <= apiMax = APIObjectType $ toEnum n
        | n == apiMax + 1 = HugePageObject
        | n == apiMax + 2 = VSpaceObject
        | n == apiMax + 3 = SmallPageObject
        | n == apiMax + 4 = LargePageObject
        | n == apiMax + 5 = PageTableObject
        | n == apiMax + 6 = VCPUObject
        | otherwise = error "toEnum out of range for AArch64.ObjectType"
        where apiMax = fromEnum (maxBound :: APIObjectType)

fromAPIType = APIObjectType

toAPIType (APIObjectType a) = Just a
toAPIType _ = Nothing

pageType = SmallPageObject

tcbBlockSizeBits :: Int
tcbBlockSizeBits = 11

apiGetObjectSize :: APIObjectType -> Int -> Int
apiGetObjectSize Untyped size = size
apiGetObjectSize TCBObject _ = tcbBlockSizeBits
apiGetObjectSize EndpointObject _ = epSizeBits
apiGetObjectSize NotificationObject _ = ntfnSizeBits
apiGetObjectSize CapTableObject size = cteSizeBits + size

getObjectSize :: ObjectType -> Int -> Int
getObjectSize PageTableObject _ = ptBits NormalPT_T
getObjectSize VSpaceObject _ = ptBits VSRootPT_T
getObjectSize SmallPageObject _ = pageBitsForSize ARMSmallPage
getObjectSize LargePageObject _ = pageBitsForSize ARMLargePage
getObjectSize HugePageObject _ = pageBitsForSize ARMHugePage
getObjectSize VCPUObject _ = vcpuBits
getObjectSize (APIObjectType apiObjectType) size = apiGetObjectSize apiObjectType size

isFrameType :: ObjectType -> Bool
isFrameType SmallPageObject = True
isFrameType LargePageObject = True
isFrameType HugePageObject = True
isFrameType _ = False
