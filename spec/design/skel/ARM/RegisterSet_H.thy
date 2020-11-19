(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Register Set"

theory RegisterSet_H
imports
  "Lib.HaskellLib_H"
  MachineOps
begin
context Arch begin arch_global_naming (H)

definition newFPUState :: "fpu_state" where
  "newFPUState \<equiv> FPUState (K 0) 0 0 "

definition
  newContext :: "user_context"
where
 "newContext \<equiv> UserContext newFPUState ((K 0) aLU initContext)"

end
end
