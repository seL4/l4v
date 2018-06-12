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

-- There are FIXME RISCV 64bit-specific object types: FIXME RISCV

data ObjectType
    = APIObjectType APIObjectType
    | FIXMERISCVObject
    deriving (Show, Eq)

instance Bounded ObjectType where
    minBound = APIObjectType minBound
    maxBound = FIXMERISCVObject -- FIXME RISCV TODO

instance Enum ObjectType where
    fromEnum e = case e of
        APIObjectType a -> fromEnum a
        FIXMERISCVObject -> apiMax + 1 -- FIXME RISCV TODO
        where apiMax = fromEnum (maxBound :: APIObjectType)
    toEnum n
        | n <= apiMax = APIObjectType $ toEnum n
        | n == apiMax + 1 = FIXMERISCVObject -- FIXME RISCV TODO
        | otherwise = error "toEnum out of range for RISCV.ObjectType"
        where apiMax = fromEnum (maxBound :: APIObjectType)

fromAPIType = APIObjectType

toAPIType (APIObjectType a) = Just a
toAPIType _ = Nothing

pageType = error "FIXME RISCV TODO"

getObjectSize :: ObjectType -> Int -> Int
getObjectSize FIXMERISCVObject _ = error "FIXME RISCV TODO"
getObjectSize (APIObjectType apiObjectType) size = apiGetObjectSize apiObjectType size

isFrameType :: ObjectType -> Bool
isFrameType FIXMERISCVObject = error "FIXME RISCV TODO"
isFrameType _ = False
