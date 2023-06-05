--
-- Copyright 2023, Proofcraft Pty Ltd
--
-- SPDX-License-Identifier: GPL-2.0-only
--

-- This module contains architecture-specific code for PSpace, in particular
-- for potential ghost state updates when deleting objects.

module SEL4.Model.PSpace.ARM(deleteGhost) where

import Prelude hiding (Word)
import SEL4.Model.StateData
import SEL4.Machine.RegisterSet

deleteGhost :: PPtr a -> Int -> Kernel ()
deleteGhost ptr bits = return ()
