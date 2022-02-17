(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Register Set"

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory RegisterSet_H
imports
  "Lib.HaskellLib_H"
  MachineOps
begin
context Arch begin global_naming AARCH64_H

definition
  newContext :: "user_context"
where
 "newContext \<equiv> UserContext ((K 0) aLU initContext)"

end
end
