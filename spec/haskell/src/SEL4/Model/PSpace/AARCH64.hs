--
-- Copyright 2023, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains architecture-specific code for PSpace, in particular
-- for potential ghost state updates when deleting objects.

module SEL4.Model.PSpace.AARCH64(deleteGhost) where

import Prelude hiding (Word)
import SEL4.Model.StateData
import SEL4.Model.StateData.AARCH64
import SEL4.Machine.RegisterSet
import SEL4.Machine.Hardware.AARCH64 (PT_Type)

import Data.Bits

-- an assertion like cNodePartialOverlap, but for page tables, defined in Refine
pTablePartialOverlap :: (Word -> Maybe PT_Type) -> (Word -> Bool) -> Bool
pTablePartialOverlap _ _ = False

deleteGhost :: PPtr a -> Int -> Kernel ()
deleteGhost ptr bits = do
    let inRange = (\x -> x .&. ((- mask bits) - 1) == fromPPtr ptr)
    ptTypes <- gets (gsPTTypes . ksArchState)
    let ptTypes' = (\x -> if inRange x then Nothing else ptTypes x)
    stateAssert (\ks -> not (pTablePartialOverlap ptTypes inRange))
        "Object deletion would split page tables"
    modify (\ks -> ks { ksArchState = (ksArchState ks) { gsPTTypes = ptTypes' } })
